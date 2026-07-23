#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const SCRIPT_DIR = path.dirname(fileURLToPath(import.meta.url));
const CONFORMANCE_DIR = path.resolve(SCRIPT_DIR, '..');

const DEFAULT_CASE_DIR = path.join(CONFORMANCE_DIR, 'graphql-js/cases');

const args = parseArgs(process.argv.slice(2));
const caseDir = args.cases === undefined ? DEFAULT_CASE_DIR : path.resolve(args.cases);
const graphql = await importGraphQL();

const suiteFiles = fs
  .readdirSync(caseDir, { withFileTypes: true })
  .filter((entry) => entry.isFile() && entry.name.endsWith('.json'))
  .map((entry) => path.join(caseDir, entry.name))
  .sort();

const reports = [];
let failures = 0;

for (const suiteFile of suiteFiles) {
  const suite = JSON.parse(fs.readFileSync(suiteFile, 'utf8'));
  let changed = false;

  for (const testCase of suite.cases ?? []) {
    const actual = await runCase(testCase);
    const expected = testCase.expected;
    const ok = expected !== undefined && stableJson(actual) === stableJson(expected);

    if (args.update) {
      testCase.expected = actual;
      changed = true;
    } else if (args.check && !ok) {
      failures += 1;
      reports.push({ id: testCase.id, expected, actual });
    } else if (!args.check) {
      reports.push({ id: testCase.id, actual });
    }
  }

  if (changed) {
    fs.writeFileSync(suiteFile, `${JSON.stringify(suite, null, 2)}\n`);
    reports.push({ updated: suiteFile });
  }
}

if (args.check) {
  if (failures > 0) {
    console.error(JSON.stringify(reports, null, 2));
    process.exit(1);
  }
  console.log(`graphql-js oracle projection matched ${countCases(suiteFiles)} cases`);
} else {
  console.log(JSON.stringify(reports, null, 2));
}

async function runCase(testCase) {
  if (typeof testCase.graphqlSource !== 'string') {
    throw new Error(`${testCase.id}: graphqlSource is required for oracle execution`);
  }

  const schema = buildSchema(testCase);
  const document = graphql.parse(testCase.graphqlSource);
  const rootValue = toJsResolverValue(testCase.source);
  const variableValues = Object.fromEntries(
    (testCase.variables ?? []).map((variable) => [
      variable.name,
      toJsInputValue(variable.value),
    ]),
  );

  const result = await graphql.execute({
    schema,
    document,
    rootValue,
    variableValues,
  });

  return {
    data: normalizeData(result.data ?? null),
    errorCount: result.errors?.length ?? 0,
  };
}

function buildSchema(testCase) {
  const typeDefinitions = new Map(
    (testCase.schema.types ?? []).map((typeDef) => [typeDef.name, typeDef]),
  );
  const cache = new Map();

  const schema = new graphql.GraphQLSchema({
    query: getNamedType(testCase.schema.queryType),
    types: [...typeDefinitions.values()]
      .filter((typeDef) => typeDef.name !== testCase.schema.queryType)
      .map((typeDef) => getNamedType(typeDef.name)),
  });
  return schema;

  function getNamedType(name) {
    if (cache.has(name)) {
      return cache.get(name);
    }

    const builtin = builtinScalar(name);
    if (builtin !== undefined) {
      return builtin;
    }

    const typeDef = typeDefinitions.get(name);
    if (typeDef === undefined) {
      throw new Error(`${testCase.id}: unknown type ${name}`);
    }

    let type;
    switch (typeDef.kind) {
      case 'object':
        type = new graphql.GraphQLObjectType({
          name: typeDef.name,
          interfaces: () => (typeDef.interfaces ?? []).map(getNamedType),
          fields: () => buildFields(typeDef.fields ?? []),
        });
        break;
      case 'interface':
        type = new graphql.GraphQLInterfaceType({
          name: typeDef.name,
          interfaces: () => (typeDef.interfaces ?? []).map(getNamedType),
          fields: () => buildFields(typeDef.fields ?? []),
          resolveType: (source) => source?.__typename,
        });
        break;
      case 'union':
        type = new graphql.GraphQLUnionType({
          name: typeDef.name,
          types: () => (typeDef.members ?? []).map(getNamedType),
          resolveType: (source) => source?.__typename,
        });
        break;
      case 'enum':
        type = new graphql.GraphQLEnumType({
          name: typeDef.name,
          values: Object.fromEntries(
            (typeDef.values ?? []).map((value) => [value, { value }]),
          ),
        });
        break;
      case 'customScalar':
        type = new graphql.GraphQLScalarType({
          name: typeDef.name,
          serialize: (value) => value,
        });
        break;
      case 'inputObject':
        type = new graphql.GraphQLInputObjectType({
          name: typeDef.name,
          fields: () => buildInputFields(typeDef.inputFields ?? []),
        });
        break;
      default:
        throw new Error(`${testCase.id}: unsupported type kind ${typeDef.kind}`);
    }

    cache.set(name, type);
    return type;
  }

  function buildFields(fields) {
    return Object.fromEntries(
      fields.map((field) => [
        field.name,
        {
          type: buildTypeRef(field.type),
          args: buildInputFields(field.arguments ?? []),
          resolve: (source, _args, _context, info) =>
            resolveFixtureField(testCase, source, info.parentType.name, info.fieldName),
        },
      ]),
    );
  }

  function buildInputFields(fields) {
    return Object.fromEntries(
      fields.map((field) => [
        field.name,
        {
          type: buildTypeRef(field.type),
          defaultValue:
            field.defaultValue === undefined
              ? undefined
              : toJsInputValue(field.defaultValue),
        },
      ]),
    );
  }

  function buildTypeRef(typeRef) {
    switch (typeRef.kind) {
      case 'named':
        return getNamedType(typeRef.name);
      case 'list':
        return new graphql.GraphQLList(buildTypeRef(typeRef.of));
      case 'nonNull':
        return new graphql.GraphQLNonNull(buildTypeRef(typeRef.of));
      default:
        throw new Error(`${testCase.id}: unsupported type ref kind ${typeRef.kind}`);
    }
  }
}

function resolveFixtureField(testCase, source, parentType, fieldName) {
  const sourceRef = source?.__ref;
  const resolver = (testCase.resolvers ?? []).find((candidate) => {
    if (candidate.parentType !== parentType || candidate.fieldName !== fieldName) {
      return false;
    }
    return candidate.sourceRef === undefined || candidate.sourceRef === sourceRef;
  });

  if (resolver === undefined) {
    return null;
  }
  if (resolver.returns?.kind === 'error') {
    throw new Error(resolver.returns.message ?? 'fixture resolver error');
  }
  return toJsResolverValue(resolver.returns);
}

function toJsResolverValue(value) {
  switch (value.kind) {
    case 'null':
      return null;
    case 'scalar':
      return value.value;
    case 'object':
      return { __typename: value.typeName, __ref: value.ref };
    case 'list':
      return (value.values ?? []).map(toJsResolverValue);
    default:
      throw new Error(`unsupported resolver value kind: ${value.kind}`);
  }
}

function toJsInputValue(value) {
  switch (value.kind) {
    case 'null':
      return null;
    case 'int':
    case 'float':
    case 'string':
    case 'boolean':
    case 'enum':
      return value.value;
    case 'list':
      return (value.values ?? []).map(toJsInputValue);
    case 'object':
      return Object.fromEntries(
        (value.fields ?? []).map((field) => [field.name, toJsInputValue(field.value)]),
      );
    default:
      throw new Error(`unsupported input value kind: ${value.kind}`);
  }
}

function normalizeData(value) {
  if (value === null || value === undefined) {
    return { kind: 'null' };
  }
  if (Array.isArray(value)) {
    return { kind: 'list', values: value.map(normalizeData) };
  }
  if (typeof value === 'object') {
    return {
      kind: 'object',
      fields: Object.entries(value).map(([name, fieldValue]) => ({
        name,
        value: normalizeData(fieldValue),
      })),
    };
  }
  return { kind: 'scalar', value: String(value) };
}

function builtinScalar(name) {
  switch (name) {
    case 'Int':
      return graphql.GraphQLInt;
    case 'Float':
      return graphql.GraphQLFloat;
    case 'String':
      return graphql.GraphQLString;
    case 'Boolean':
      return graphql.GraphQLBoolean;
    case 'ID':
      return graphql.GraphQLID;
    default:
      return undefined;
  }
}

async function importGraphQL() {
  const specifier = process.env.GRAPHQL_JS_MODULE ?? 'graphql';
  try {
    return await import(asImportSpecifier(specifier));
  } catch (error) {
    throw new Error(
      [
        `Unable to import graphql-js module ${JSON.stringify(specifier)}.`,
        'Install graphql or set GRAPHQL_JS_MODULE to an importable graphql-js module.',
        `Original error: ${error.message}`,
      ].join('\n'),
    );
  }
}

function asImportSpecifier(specifier) {
  return path.isAbsolute(specifier) ? pathToFileURL(specifier).href : specifier;
}

function parseArgs(argv) {
  const parsed = { check: false, update: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--cases') {
      parsed.cases = argv[++index];
    } else if (arg === '--check') {
      parsed.check = true;
    } else if (arg === '--update') {
      parsed.update = true;
    } else if (arg === '--help' || arg === '-h') {
      console.log(
        [
          'Usage: node conformance/scripts/graphql-js-oracle.mjs [--cases DIR] [--check] [--update]',
          '',
          'Set GRAPHQL_JS_MODULE to choose the graphql-js import specifier.',
        ].join('\n'),
      );
      process.exit(0);
    } else {
      throw new Error(`unknown argument: ${arg}`);
    }
  }
  return parsed;
}

function stableJson(value) {
  return JSON.stringify(value);
}

function countCases(files) {
  return files.reduce((count, file) => {
    const suite = JSON.parse(fs.readFileSync(file, 'utf8'));
    return count + (suite.cases?.length ?? 0);
  }, 0);
}

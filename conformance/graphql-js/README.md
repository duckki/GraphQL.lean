# graphql-js Conformance Fixtures

This directory contains neutral fixtures used to compare the proof-facing
`GraphQL.Execution` model with selected `graphql-js` execution tests.

Install the pinned graphql-js oracle dependency once with:

```sh
npm install
```

The checked-in Lean tests are generated from `cases/*.json`:

```sh
node scripts/gen-graphql-js-conformance.mjs
lake build Tests.Conformance.Execution
```

Named-fragment execution fixtures live under `named-fragment-cases/` and target
the separate `GraphQL.NamedFragment.Execution` model:

```sh
node scripts/gen-graphql-js-conformance.mjs \
  --cases conformance/graphql-js/named-fragment-cases \
  --target named-fragment
lake build Tests.Conformance.NamedFragment
```

The optional oracle script can run the same fixtures through graphql-js and
compare the projected result:

```sh
npm run oracle:graphql-js
```

To check only the named-fragment fixtures:

```sh
npm run oracle:graphql-js:named-fragment
```

For a source checkout of graphql-js 17.x, run the oracle with Node 22 or newer
and set `GRAPHQL_JS_MODULE` to an importable module specifier for that checkout.
The oracle projection compares ordered `data` plus `errors.length`; it does not
compare messages, paths, locations, extensions, or host-runtime async behavior.

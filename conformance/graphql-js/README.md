# graphql-js Conformance Fixtures

This directory contains neutral fixtures used to compare the proof-facing
`GraphQL.Execution` model with selected `graphql-js` execution tests.

The checked-in Lean tests are generated from `cases/*.json`:

```sh
node scripts/gen-graphql-js-conformance.mjs
lake build Tests.Conformance.Execution
```

The optional oracle script can run the same fixtures through graphql-js and
compare the projected result:

```sh
GRAPHQL_JS_MODULE=graphql node scripts/graphql-js-oracle.mjs --check
```

For a source checkout of graphql-js 17.x, run the oracle with Node 22 or newer
and set `GRAPHQL_JS_MODULE` to an importable module specifier for that checkout.
The oracle projection compares ordered `data` plus `errors.length`; it does not
compare messages, paths, locations, extensions, or host-runtime async behavior.

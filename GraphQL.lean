import GraphQL.Schema
import GraphQL.SchemaWellFormedness
import GraphQL.Operation
import GraphQL.Semantic
import GraphQL.FieldMerge
import GraphQL.Validation
import GraphQL.NormalForm
import GraphQL.ResponseShape
import GraphQL.Execution
import GraphQL.Minimization

/-!
Spec reference: GraphQL September 2025.
- 2 Language, 3 Type System, 5 Validation, 6 Execution, and 7 Response: this root module
  re-exports the partial GraphQL formalization modules.
- It is an import surface only; fidelity is documented in the individual modules.
-/

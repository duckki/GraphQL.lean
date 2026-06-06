import GraphQL.Schema
import GraphQL.SchemaWellFormedness
import GraphQL.SchemaWellFormedness.FieldLookup
import GraphQL.SchemaWellFormedness.PossibleObjectImplementation
import GraphQL.Operation
import GraphQL.Validation
import GraphQL.Validation.SelectionValidity
import GraphQL.Validation.FieldMerge
import GraphQL.Execution
import GraphQL.Execution.FieldCollection
import GraphQL.DataModel
import GraphQL.DataModel.Store
import GraphQL.NormalForm
import GraphQL.NormalForm.GroundTypeNormalization
import GraphQL.NormalForm.GroundTypeNormalization.FieldCollection
import GraphQL.NormalForm.GroundTypeNormalization.Semantics

/-!
Spec reference: GraphQL September 2025.
- 2 Language, 3 Type System, 5 Validation, 6 Execution, and 7 Response: this root module
  re-exports the partial GraphQL formalization modules.
- Import order follows the intended reading order for the existing scoped model:
  syntax/type system, validation, execution/data semantics, then project-specific normal
  form machinery.
- It is an import surface only; fidelity is documented in the individual modules.
-/

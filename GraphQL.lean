import GraphQL.Schema
import GraphQL.SchemaWellFormedness
import GraphQL.SchemaWellFormedness.FieldLookup
import GraphQL.SchemaWellFormedness.PossibleTypes
import GraphQL.Operation
import GraphQL.Validation
import GraphQL.Validation.SelectionValidity
import GraphQL.Validation.FieldMerge
import GraphQL.Execution
import GraphQL.Execution.FieldCollection
import GraphQL.DataModel.ObjectRef
import GraphQL.DataModel
import GraphQL.DataModel.Store
import GraphQL.DataModel.StoreValueInclusion
import GraphQL.NormalForm
import GraphQL.NormalForm.GroundTypeNormalization.Normality
import GraphQL.NormalForm.GroundTypeNormalization.Semantics
import GraphQL.NormalForm.GroundTypeNormalization.Validity
import GraphQL.NormalForm.GroundTypeLifting.OperationSemantics
import GraphQL.NormalForm.CompleteNormalization.OperationNormality
import GraphQL.NormalForm.CompleteNormalization.Semantics
import GraphQL.NormalForm.CompleteNormalization.Validity

/-!
Spec reference: GraphQL September 2025.
- 2 Language, 3 Type System, 5 Validation, 6 Execution, and 7 Response: this root module
  re-exports the partial GraphQL formalization modules.
- Import order follows the intended reading order for the existing scoped model:
  syntax/type system, validation, execution/data semantics, then project-specific normal
  form machinery.
- Complete-normalization proof modules expose semantic preservation, normality, and
  validity under explicit retained-empty-composite-field assumptions.
- It is an import surface only; fidelity is documented in the individual modules.
-/

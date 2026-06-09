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
import GraphQL.NormalForm.GroundTypeNormalization.FieldCollection
import GraphQL.NormalForm.GroundTypeNormalization.Semantics
import GraphQL.NormalForm.GroundTypeLifting.OperationSemantics
import GraphQL.NormalForm.CompleteNormalization.Variables
import GraphQL.NormalForm.CompleteNormalization.DirectiveSemantics
import GraphQL.NormalForm.CompleteNormalization.BoolCaseWrappers
import GraphQL.NormalForm.CompleteNormalization.StaticCollection
import GraphQL.NormalForm.CompleteNormalization.Normality
import GraphQL.NormalForm.CompleteNormalization.OperationVariables
import GraphQL.NormalForm.CompleteNormalization.OperationWrappers
import GraphQL.NormalForm.CompleteNormalization.ScopedSelections
import GraphQL.NormalForm.CompleteNormalization.FieldOutput
import GraphQL.NormalForm.CompleteNormalization.ExecutionPrelude
import GraphQL.NormalForm.CompleteNormalization.FieldDirectiveExecution
import GraphQL.NormalForm.CompleteNormalization.InlineDirectiveExecution
import GraphQL.NormalForm.CompleteNormalization.StaticFieldGroups
import GraphQL.NormalForm.CompleteNormalization.StaticCollectionExecution
import GraphQL.NormalForm.CompleteNormalization.ScopedStaticExecution
import GraphQL.NormalForm.CompleteNormalization.StaticMergeReadiness
import GraphQL.NormalForm.CompleteNormalization.BoolCaseRuntime
import GraphQL.NormalForm.CompleteNormalization.RuntimeTypes
import GraphQL.NormalForm.CompleteNormalization.BoolCaseChildSemantics
import GraphQL.NormalForm.CompleteNormalization.ScopedResolverSemantics
import GraphQL.NormalForm.CompleteNormalization.ChildCompletion
import GraphQL.NormalForm.CompleteNormalization.RootSemantics

/-!
Spec reference: GraphQL September 2025.
- 2 Language, 3 Type System, 5 Validation, 6 Execution, and 7 Response: this root module
  re-exports the partial GraphQL formalization modules.
- Import order follows the intended reading order for the existing scoped model:
  syntax/type system, validation, execution/data semantics, then project-specific normal
  form machinery.
- It is an import surface only; fidelity is documented in the individual modules.
-/

import GraphQL.SchemaWellFormedness.PossibleTypes
import GraphQL.Validation.SelectionValidity
import GraphQL.Validation.FieldMerge
import GraphQL.Execution.Data
import GraphQL.Execution.ResolverValue
import GraphQL.Execution.FieldCollection
import GraphQL.Execution.SemanticEquivalence
import GraphQL.NamedFragment.Validation
import GraphQL.NamedFragment.Execution
import GraphQL.NamedFragment.Inline.Basic
import GraphQL.NamedFragment.Semantics.Inline
import GraphQL.NamedFragment.Semantics.Validation
import GraphQL.Algorithms.ExecutionUngrouped.Semantics
import GraphQL.Algorithms.ExecutionUngrouped.Equivalence
import GraphQL.NormalForm.GroundTypeNormalization.Semantics
import GraphQL.NormalForm.GroundTypeNormalization.Validity
import GraphQL.NormalForm.CompleteNormalization.OperationNormality
import GraphQL.NormalForm.CompleteNormalization.Semantics
import GraphQL.NormalForm.CompleteNormalization.Validity
import GraphQL.NormalForm.CompleteNormalization.Uniqueness

/-!
Spec reference: GraphQL September 2025.
- 2 Language, 3 Type System, 5 Validation, 6 Execution, and 7 Response: this root module
  re-exports the partial GraphQL formalization modules.
- This root module intentionally imports public surfaces and aggregators rather than
  every internal proof module. Import implementation modules directly when working on
  localized proof internals.
- Import order follows the intended reading order for the scoped model: schema and
  validation support, execution, ungrouped execution semantics, then normal-form theorem
  surfaces.
-/

import Tests.NormalForm.Common

namespace GraphQL
namespace Tests
namespace NormalForm

open GraphQL.NormalForm

def completeNormalizationStaticImpossibleInputQuery : Operation :=
  operationWith
    [.field "hero" "hero" [] [.skip (.boolean true)] [.field "id" "id" [] [] []]]

theorem completeNormalizationStaticImpossibleEmpty
    : operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationStaticImpossibleInputQuery)
        (operationWith [])
      = true := by
  native_decide

def completeNormalizationNestedImpossibleInputQuery : Operation :=
  operationWith
    [.field "hero" "hero" [] [.skip (.variable "x")]
      [.field "id" "id" [] [.include (.variable "x")] []]]

theorem completeNormalizationNestedImpossibleEmpty
    : operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationNestedImpossibleInputQuery)
        (operationWith [])
      = true := by
  native_decide

def completeNormalizationNestedFragmentImpossibleInputQuery : Operation :=
  operationWith
    [.field "hero" "hero" [] [.skip (.variable "x")]
      [.inlineFragment (some "Human") []
        [.field "id" "id" [] [.include (.variable "x")] []]]]

theorem completeNormalizationNestedFragmentImpossibleEmpty
    : operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationNestedFragmentImpossibleInputQuery)
        (operationWith [])
      = true := by
  native_decide

end NormalForm
end Tests
end GraphQL

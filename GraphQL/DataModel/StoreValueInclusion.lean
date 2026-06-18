import GraphQL.DataModel.Store
import GraphQL.SchemaWellFormedness.PossibleTypes

/-!
Store-backed resolved-value inclusion lemmas.
-/
namespace GraphQL

namespace DataModel

namespace Store

def executionValueObjectsInclude (schema : Schema) (parentType : Name) :
    Execution.Value ObjectRef -> Prop
  | .object runtimeType _ref =>
      schema.typeIncludesObjectBool parentType runtimeType = true
  | .list values =>
      ∀ value, value ∈ values ->
        executionValueObjectsInclude schema parentType value
  | _ => True

private theorem executionValueObjectsInclude_mono
    (schema : Schema) {left right : Name} :
    (∀ runtimeType,
      schema.typeIncludesObjectBool left runtimeType = true ->
        schema.typeIncludesObjectBool right runtimeType = true) ->
      ∀ value : Execution.Value ObjectRef,
        executionValueObjectsInclude schema left value ->
          executionValueObjectsInclude schema right value
  | hsubtype, .null, _hinclude => by
      simp [executionValueObjectsInclude]
  | hsubtype, .scalar _value, _hinclude => by
      simp [executionValueObjectsInclude]
  | hsubtype, .object runtimeType _ref, hinclude => by
      simpa [executionValueObjectsInclude] using
        hsubtype runtimeType
          (by simpa [executionValueObjectsInclude] using hinclude)
  | hsubtype, .list values, hinclude => by
      have hinclude' :
          ∀ value, value ∈ values ->
            executionValueObjectsInclude schema left value := by
        simpa [executionValueObjectsInclude] using hinclude
      simp [executionValueObjectsInclude]
      intro value hvalue
      exact executionValueObjectsInclude_mono schema hsubtype value
        (hinclude' value hvalue)

private theorem executionValueObjectsInclude_of_conformsToType
    (schema : Schema) :
    ∀ value typeRef,
      valueConformsToType schema value typeRef ->
        executionValueObjectsInclude schema typeRef.namedType value
  | .null, .named _typeName, _hconforms => by
      simp [executionValueObjectsInclude]
  | .null, .list _inner, _hconforms => by
      simp [executionValueObjectsInclude]
  | .null, .nonNull _inner, hconforms => by
      cases hconforms
  | .scalar _value, .named _typeName, _hconforms => by
      simp [executionValueObjectsInclude]
  | .scalar value, .nonNull inner, hconforms => by
      exact executionValueObjectsInclude_of_conformsToType schema
        (.scalar value) inner hconforms
  | .scalar _value, .list _inner, hconforms => by
      cases hconforms
  | .object runtimeType _ref, .named typeName, hconforms => by
      simpa [executionValueObjectsInclude] using
        (show schema.typeIncludesObjectBool typeName runtimeType = true from
          List.contains_iff_mem.mpr hconforms)
  | .object runtimeType ref, .nonNull inner, hconforms => by
      simpa [TypeRef.namedType, executionValueObjectsInclude] using
        executionValueObjectsInclude_of_conformsToType schema
          (.object runtimeType ref) inner hconforms
  | .object _runtimeType _ref, .list _inner, hconforms => by
      cases hconforms
  | .list values, .list inner, hconforms => by
      simp [TypeRef.namedType, executionValueObjectsInclude]
      intro value hvalue
      exact executionValueObjectsInclude_of_conformsToType schema value inner
        (hconforms value hvalue)
  | .list values, .nonNull inner, hconforms => by
      simpa [TypeRef.namedType, executionValueObjectsInclude] using
        executionValueObjectsInclude_of_conformsToType schema
          (.list values) inner hconforms
  | .list _values, .named _typeName, hconforms => by
      cases hconforms

private theorem executionValueObjectsInclude_list_map_edges
    (schema : Schema) (parentType : Name)
    (edges : List ObjectEdge) :
    (∀ edge, edge ∈ edges ->
      schema.typeIncludesObjectBool parentType edge.targetType = true) ->
      executionValueObjectsInclude schema parentType
        (.list (edges.map (fun edge =>
          Execution.Value.object edge.targetType
            (some (objectRefOfId edge.targetId))))) := by
  intro hedges
  simp [executionValueObjectsInclude]
  intro edge hedge
  exact hedges edge hedge

private theorem mem_insertEdgeByIndex_self_or_mem
    (edge candidate : ObjectEdge) :
    ∀ edges,
      edge ∈ insertEdgeByIndex candidate edges ->
        edge = candidate ∨ edge ∈ edges
  | [], hmem => by
      simp [insertEdgeByIndex] at hmem
      exact Or.inl hmem
  | head :: rest, hmem => by
      by_cases hle : candidate.index?.getD 0 <= head.index?.getD 0
      · simp [insertEdgeByIndex, hle] at hmem
        exact hmem.elim Or.inl (fun htail => Or.inr (by simpa using htail))
      · have hgt : ¬ candidate.index?.getD 0 <= head.index?.getD 0 :=
          hle
        simp [insertEdgeByIndex, hgt] at hmem
        rcases hmem with hhead | hinserted
        · exact Or.inr (by simp [hhead])
        · rcases mem_insertEdgeByIndex_self_or_mem edge candidate rest
            hinserted with hcandidate | hrest
          · exact Or.inl hcandidate
          · exact Or.inr (by simp [hrest])

private theorem mem_sortEdgesByIndex_mem
    (edge : ObjectEdge) :
    ∀ edges,
      edge ∈ sortEdgesByIndex edges ->
        edge ∈ edges
  | [], hmem => by
      simp [sortEdgesByIndex] at hmem
  | head :: rest, hmem => by
      simp [sortEdgesByIndex] at hmem
      rcases mem_insertEdgeByIndex_self_or_mem edge head
          (sortEdgesByIndex rest) hmem with hhead | hrest
      · simp [hhead]
      · exact List.mem_cons_of_mem head
          (mem_sortEdgesByIndex_mem edge rest hrest)

private theorem mem_indexedMatchingEdges_mem_edges
    (store : DataModel.Store) (sourceId : ObjectId)
    (field : FieldAccess) (edge : ObjectEdge) :
    edge ∈ store.indexedMatchingEdges sourceId field ->
      edge ∈ store.edges := by
  intro hmem
  have hunordered :
      edge ∈ store.indexedMatchingEdgesUnsorted sourceId field :=
    mem_sortEdgesByIndex_mem edge
      (store.indexedMatchingEdgesUnsorted sourceId field) hmem
  simp [indexedMatchingEdgesUnsorted, matchingEdges] at hunordered
  exact hunordered.1

private theorem mem_indexedMatchingEdges_matches
    (store : DataModel.Store) (sourceId : ObjectId)
    (field : FieldAccess) (edge : ObjectEdge) :
    edge ∈ store.indexedMatchingEdges sourceId field ->
      edge.matchesField sourceId field = true := by
  intro hmem
  have hunordered :
      edge ∈ store.indexedMatchingEdgesUnsorted sourceId field :=
    mem_sortEdgesByIndex_mem edge
      (store.indexedMatchingEdgesUnsorted sourceId field) hmem
  simp [indexedMatchingEdgesUnsorted, matchingEdges] at hunordered
  exact hunordered.2.2

private theorem firstMatchingEdge?_some_mem
    (store : DataModel.Store) (sourceId : ObjectId)
    (field : FieldAccess) (index? : Option Nat)
    (edge : ObjectEdge) :
    store.firstMatchingEdge? sourceId field index? = some edge ->
      edge ∈ store.edges := by
  intro hlookup
  exact List.mem_of_find?_eq_some hlookup

private theorem firstMatchingEdge?_some_matches
    (store : DataModel.Store) (sourceId : ObjectId)
    (field : FieldAccess) (index? : Option Nat)
    (edge : ObjectEdge) :
    store.firstMatchingEdge? sourceId field index? = some edge ->
      edge.matchesField sourceId field = true
        ∧ (edge.index? == index?) = true := by
  intro hlookup
  have hpredicate := List.find?_some hlookup
  simpa [firstMatchingEdge?] using hpredicate

private theorem objectEdge_matchesField_sourceId
    (edge : ObjectEdge) (sourceId : ObjectId)
    (field : FieldAccess) :
    edge.matchesField sourceId field = true ->
      edge.sourceId = sourceId := by
  intro hmatch
  simp [ObjectEdge.matchesField] at hmatch
  exact hmatch.1

private theorem objectEdge_matchesField_fieldName
    (edge : ObjectEdge) (sourceId : ObjectId)
    (field : FieldAccess) :
    edge.matchesField sourceId field = true ->
      edge.field.name = field.name := by
  intro hmatch
  simp [ObjectEdge.matchesField, FieldAccess.eqBool] at hmatch
  exact hmatch.2.1

private theorem edge_targets_include_of_lookupField
    (schema : Schema) (store : DataModel.Store)
    (sourceNode : ObjectNode)
    (fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) :
    store.wellTyped schema ->
    sourceNode ∈ store.allNodes ->
    schema.lookupField sourceNode.typeName fieldName = some fieldDefinition ->
    (let field := fieldAccess fieldName arguments
     ∀ edge, edge ∈ store.edges ->
      edge.matchesField sourceNode.id field = true ->
        schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
          edge.targetType = true) := by
  intro hstore hsourceMem hlookup field edge hedge hmatches
  have hedgeWell := hstore.2.2.2.1 edge hedge
  rcases hedgeWell with
    ⟨storedSource, targetNode, implementationDefinition, hsourceLookup,
      _htargetLookup, htargetType, himplementationLookup, _hpossible,
      _harguments, _hlistLike, htarget⟩
  have hsourceId :
      edge.sourceId = sourceNode.id :=
    objectEdge_matchesField_sourceId edge sourceNode.id field hmatches
  have hsourceLookupCurrent :
      store.lookupNode? sourceNode.id = some sourceNode :=
    lookupNode?_some_of_mem_unique store sourceNode hstore.2.1 hsourceMem
  have hsourceLookupMatched :
      store.lookupNode? edge.sourceId = some sourceNode := by
    simpa [hsourceId] using hsourceLookupCurrent
  rw [hsourceLookupMatched] at hsourceLookup
  cases hsourceLookup
  have hfieldName :
      edge.field.name = fieldName := by
    have hfield := objectEdge_matchesField_fieldName edge sourceNode.id field
      hmatches
    simpa [field, fieldAccess] using hfield
  have himplementationLookup' :
      schema.lookupField sourceNode.typeName fieldName =
        some implementationDefinition := by
    simpa [hfieldName] using himplementationLookup
  rw [hlookup] at himplementationLookup'
  cases himplementationLookup'
  change (schema.getPossibleTypes fieldDefinition.outputType.namedType).contains
    edge.targetType = true
  simpa [htargetType] using List.contains_iff_mem.mpr htarget

private theorem resolveValue_objectsInclude_of_runtime_lookupField
    (schema : Schema) (store : DataModel.Store)
    (runtimeType : Name)
    (fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) :
    store.wellTyped schema ->
    schema.lookupField runtimeType fieldName = some fieldDefinition ->
      executionValueObjectsInclude schema fieldDefinition.outputType.namedType
        (store.resolveValue schema fieldName arguments runtimeType) := by
  intro hstore hlookup
  cases hnode : store.firstNodeWithType? runtimeType with
  | none =>
      simp [resolveValue, hnode, executionValueObjectsInclude]
  | some node =>
      have hnodeType : node.typeName = runtimeType :=
        firstNodeWithType?_some_typeName store hnode
      have hlookupNode :
          schema.lookupField node.typeName fieldName = some fieldDefinition := by
        simpa [hnodeType] using hlookup
      have hnodeMem : node ∈ store.allNodes :=
        firstNodeWithType?_some_mem store hnode
      have hnodeWell : node.wellTyped schema :=
        hstore.2.2.1 node hnodeMem
      let field := fieldAccess fieldName arguments
      by_cases hleaf :
          schema.getPossibleTypes fieldDefinition.outputType.namedType = []
      · cases hproperty : node.lookupProperty? field with
        | none =>
            simp [resolveValue, hnode, hlookupNode, hleaf, field, hproperty,
              resolveValueFromNode, executionValueObjectsInclude]
        | some property =>
            rcases
              ObjectNode.lookupProperty?_some_conformsToLookupField
                schema node field property hnodeWell hproperty with
              ⟨storedFieldDefinition, hstoredLookup, _hstoredLeaf,
                hconforms⟩
            have hdefinitionEq :
                storedFieldDefinition = fieldDefinition := by
              have hstoredLookup' :
                  schema.lookupField node.typeName fieldName =
                    some storedFieldDefinition := by
                simpa [field, fieldAccess] using hstoredLookup
              rw [hlookupNode] at hstoredLookup'
              cases hstoredLookup'
              rfl
            subst storedFieldDefinition
            have hinclude :=
              executionValueObjectsInclude_of_conformsToType schema
              property.toValue fieldDefinition.outputType hconforms
            simpa [resolveValue, hnode, hlookupNode, hleaf, field, hproperty,
              resolveValueFromNode] using hinclude
      · have hnonempty :
            ¬ schema.getPossibleTypes
              fieldDefinition.outputType.namedType = [] := hleaf
        by_cases hlist :
            typeRefIsListLike fieldDefinition.outputType = true
        · have hedges :
              ∀ edge, edge ∈ store.indexedMatchingEdges node.id field ->
                schema.typeIncludesObjectBool
                  fieldDefinition.outputType.namedType edge.targetType = true := by
            intro edge hedge
            exact edge_targets_include_of_lookupField schema store node
              fieldName arguments fieldDefinition hstore hnodeMem hlookupNode edge
              (mem_indexedMatchingEdges_mem_edges store node.id field edge hedge)
              (mem_indexedMatchingEdges_matches store node.id field edge hedge)
          simpa [resolveValue, hnode, hlookupNode, hnonempty, hlist,
            resolveValueFromNode, Function.comp_def] using
            executionValueObjectsInclude_list_map_edges schema
              fieldDefinition.outputType.namedType
              (store.indexedMatchingEdges node.id field) hedges
        · cases hedge :
            store.firstMatchingEdge? node.id field none with
          | none =>
              simp [resolveValue, hnode, hlookupNode, hnonempty, hlist, field,
                hedge, resolveValueFromNode, executionValueObjectsInclude]
          | some edge =>
              have hmatches :=
                (firstMatchingEdge?_some_matches store node.id field none
                  edge hedge).1
              have htarget :=
                edge_targets_include_of_lookupField schema store node
                  fieldName arguments fieldDefinition hstore hnodeMem
                  hlookupNode edge
                  (firstMatchingEdge?_some_mem store node.id field none
                    edge hedge)
                  hmatches
              simp [resolveValue, hnode, hlookupNode, hnonempty, hlist, field,
                hedge, resolveValueFromNode, executionValueObjectsInclude]
              exact htarget

private theorem resolveValueFromNode_objectsInclude_of_lookupField
    (schema : Schema) (store : DataModel.Store)
    (node : ObjectNode)
    (fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) :
    store.wellTyped schema ->
    node ∈ store.allNodes ->
    schema.lookupField node.typeName fieldName = some fieldDefinition ->
      executionValueObjectsInclude schema fieldDefinition.outputType.namedType
        (store.resolveValueFromNode schema fieldName arguments node) := by
  intro hstore hnodeMem hlookupNode
  have hnodeWell : node.wellTyped schema :=
    hstore.2.2.1 node hnodeMem
  let field := fieldAccess fieldName arguments
  by_cases hleaf :
      schema.getPossibleTypes fieldDefinition.outputType.namedType = []
  · cases hproperty : node.lookupProperty? field with
    | none =>
        simp [hlookupNode, hleaf, field, hproperty, resolveValueFromNode,
          executionValueObjectsInclude]
    | some property =>
        rcases
          ObjectNode.lookupProperty?_some_conformsToLookupField
            schema node field property hnodeWell hproperty with
          ⟨storedFieldDefinition, hstoredLookup, _hstoredLeaf,
            hconforms⟩
        have hdefinitionEq :
            storedFieldDefinition = fieldDefinition := by
          have hstoredLookup' :
              schema.lookupField node.typeName fieldName =
                some storedFieldDefinition := by
            simpa [field, fieldAccess] using hstoredLookup
          rw [hlookupNode] at hstoredLookup'
          cases hstoredLookup'
          rfl
        subst storedFieldDefinition
        have hinclude :=
          executionValueObjectsInclude_of_conformsToType schema
          property.toValue fieldDefinition.outputType hconforms
        simpa [hlookupNode, hleaf, field, hproperty, resolveValueFromNode]
          using hinclude
  · have hnonempty :
        ¬ schema.getPossibleTypes
          fieldDefinition.outputType.namedType = [] := hleaf
    by_cases hlist :
        typeRefIsListLike fieldDefinition.outputType = true
    · have hedges :
          ∀ edge, edge ∈ store.indexedMatchingEdges node.id field ->
            schema.typeIncludesObjectBool
              fieldDefinition.outputType.namedType edge.targetType = true := by
        intro edge hedge
        exact edge_targets_include_of_lookupField schema store node
          fieldName arguments fieldDefinition hstore hnodeMem hlookupNode edge
          (mem_indexedMatchingEdges_mem_edges store node.id field edge hedge)
          (mem_indexedMatchingEdges_matches store node.id field edge hedge)
      simpa [hlookupNode, hnonempty, hlist, resolveValueFromNode,
        Function.comp_def] using
        executionValueObjectsInclude_list_map_edges schema
          fieldDefinition.outputType.namedType
          (store.indexedMatchingEdges node.id field) hedges
    · cases hedge :
        store.firstMatchingEdge? node.id field none with
      | none =>
          simp [hlookupNode, hnonempty, hlist, field, hedge,
            resolveValueFromNode, executionValueObjectsInclude]
      | some edge =>
          have hmatches :=
            (firstMatchingEdge?_some_matches store node.id field none
              edge hedge).1
          have htarget :=
            edge_targets_include_of_lookupField schema store node
              fieldName arguments fieldDefinition hstore hnodeMem
              hlookupNode edge
              (firstMatchingEdge?_some_mem store node.id field none
                edge hedge)
              hmatches
          simp [hlookupNode, hnonempty, hlist, field, hedge,
            resolveValueFromNode, executionValueObjectsInclude]
          exact htarget

private theorem resolveValue_objectsInclude_of_static_lookupField
    (schema : Schema) (store : DataModel.Store)
    (parentType runtimeType : Name)
    (fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    store.wellTyped schema ->
    schema.typeIncludesObjectBool parentType runtimeType = true ->
    schema.lookupField parentType fieldName = some fieldDefinition ->
      executionValueObjectsInclude schema fieldDefinition.outputType.namedType
        (store.resolveValue schema fieldName arguments runtimeType) := by
  intro hschema hstore hinclude hlookup
  have hpossible : runtimeType ∈ schema.getPossibleTypes parentType :=
    List.contains_iff_mem.mp hinclude
  rcases
    SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_exists
      hschema hpossible hlookup with
    ⟨implementationDefinition, himplementationLookup⟩
  have himplementation :=
    resolveValue_objectsInclude_of_runtime_lookupField schema store
      runtimeType fieldName arguments implementationDefinition
      hstore himplementationLookup
  have hsubtype :
      schema.outputTypeSubtype implementationDefinition.outputType
        fieldDefinition.outputType :=
    SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
      hschema hpossible hlookup himplementationLookup
  exact executionValueObjectsInclude_mono schema
    (fun objectType hobject =>
      GraphQL.typeIncludesObjectBool_of_outputTypeSubtype_namedType schema
        hsubtype hobject)
    (store.resolveValue schema fieldName arguments runtimeType)
    himplementation

theorem resolve_objectsInclude_of_static_lookupField
    (schema : Schema) (store : DataModel.Store)
    (parentType runtimeType : Name)
    (fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    store.wellTyped schema ->
    schema.typeIncludesObjectBool parentType runtimeType = true ->
    schema.lookupField parentType fieldName = some fieldDefinition ->
      executionValueObjectsInclude schema fieldDefinition.outputType.namedType
        (store.resolve schema fieldName arguments
          (Execution.Value.object (ObjectRef := ObjectRef) runtimeType)) := by
  intro hschema hstore hinclude hlookup
  exact resolveValue_objectsInclude_of_static_lookupField schema store
    parentType runtimeType fieldName arguments fieldDefinition hschema hstore
    hinclude hlookup

theorem resolve_objectsInclude_of_static_lookupField_ref
    (schema : Schema) (store : DataModel.Store)
    (parentType runtimeType : Name)
    (ref : Option ObjectRef)
    (fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    store.wellTyped schema ->
    schema.typeIncludesObjectBool parentType runtimeType = true ->
    schema.lookupField parentType fieldName = some fieldDefinition ->
      executionValueObjectsInclude schema fieldDefinition.outputType.namedType
        (store.resolve schema fieldName arguments
          (.object runtimeType ref)) := by
  intro hschema hstore hinclude hlookup
  cases ref with
  | none =>
      simpa [DataModel.Store.resolve] using
        resolveValue_objectsInclude_of_static_lookupField schema store
          parentType runtimeType fieldName arguments fieldDefinition hschema
          hstore hinclude hlookup
  | some ref =>
      cases href : objectIdOfRef? ref with
      | none =>
          simp [objectIdOfRef?] at href
      | some sourceId =>
          cases hnode : store.lookupNode? sourceId with
          | none =>
              simp [DataModel.Store.resolve, href, hnode,
                executionValueObjectsInclude]
          | some sourceNode =>
              by_cases hmatch : sourceNode.typeName == runtimeType
              · have hsourceType : sourceNode.typeName = runtimeType :=
                  beq_iff_eq.mp hmatch
                have hpossible :
                    runtimeType ∈ schema.getPossibleTypes parentType :=
                  List.contains_iff_mem.mp hinclude
                rcases
                  SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_exists
                    hschema hpossible hlookup with
                  ⟨implementationDefinition, himplementationLookup⟩
                have hlookupNode :
                    schema.lookupField sourceNode.typeName fieldName =
                      some implementationDefinition := by
                  simpa [hsourceType] using himplementationLookup
                have hnodeMem : sourceNode ∈ store.allNodes :=
                  lookupNode?_some_mem store hnode
                have himplementation :=
                  resolveValueFromNode_objectsInclude_of_lookupField schema store
                    sourceNode fieldName arguments implementationDefinition
                    hstore hnodeMem hlookupNode
                have hsubtype :
                    schema.outputTypeSubtype implementationDefinition.outputType
                      fieldDefinition.outputType :=
                  SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
                    hschema hpossible hlookup himplementationLookup
                have hmono :=
                  executionValueObjectsInclude_mono schema
                    (fun objectType hobject =>
                      GraphQL.typeIncludesObjectBool_of_outputTypeSubtype_namedType
                        schema hsubtype hobject)
                    (store.resolveValueFromNode schema fieldName arguments
                      sourceNode)
                    himplementation
                simpa [DataModel.Store.resolve, href, hnode, hmatch] using hmono
              · simp [DataModel.Store.resolve, href, hnode, hmatch,
                  executionValueObjectsInclude]

theorem resolvers_parentType_insensitive
    (schema : Schema) (store : DataModel.Store)
    (leftParentType rightParentType fieldName : Name)
    (arguments : List Argument)
    (source : Execution.Value ObjectRef) :
    (store.resolvers schema).resolve leftParentType fieldName arguments source =
      (store.resolvers schema).resolve rightParentType fieldName arguments
        source := by
  rfl

end Store

end DataModel

end GraphQL

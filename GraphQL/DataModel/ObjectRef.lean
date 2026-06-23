/-! Store-backed object reference bridge. -/

namespace GraphQL

namespace DataModel

abbrev ObjectId := Nat

-- Store-owned resolver reference type used to instantiate `Execution.ResolverValue`.
structure ObjectRef where
  private mk ::
  id : ObjectId
deriving BEq, Repr

-- Data-model bridge for issuing resolver references backed by store object ids.
def objectRefOfId (id : ObjectId) : ObjectRef :=
  ObjectRef.mk id

-- Data-model bridge for resolving references back to store object ids.
def objectIdOfRef (ref : ObjectRef) : ObjectId :=
  ref.id

@[simp] theorem objectIdOfRef_objectRefOfId (id : ObjectId) :
    objectIdOfRef (objectRefOfId id) = id := by
  rfl

end DataModel

end GraphQL

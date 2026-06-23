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
def objectIdOfRef? (ref : ObjectRef) : Option ObjectId :=
  some ref.id

@[simp] theorem objectIdOfRef?_objectRefOfId (id : ObjectId) :
    objectIdOfRef? (objectRefOfId id) = some id := by
  rfl

@[simp] theorem objectIdOfRef?_none :
    (Option.none : Option ObjectRef).bind objectIdOfRef? = none := by
  rfl

end DataModel

end GraphQL

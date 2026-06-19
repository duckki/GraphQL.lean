import GraphQL.DataModel.FieldAccess

/-!
Proof helpers for GraphQL semantic argument-list equivalence.
-/
namespace GraphQL

namespace DataModel

namespace Argument

theorem argumentsEquivalent_left_name_mem
    {left right : List Argument} :
    Argument.argumentsEquivalent left right ->
      ∀ argument, argument ∈ left ->
        argument.name ∈ right.map Argument.name := by
  intro hequivalent argument hmem
  rcases hequivalent.1 argument hmem with
    ⟨matched, hmatchedMem, hmatchedEquivalent⟩
  exact List.mem_map.mpr
    ⟨matched, hmatchedMem, hmatchedEquivalent.1.symm⟩

theorem argumentsEquivalent_right_name_mem
    {left right : List Argument} :
    Argument.argumentsEquivalent left right ->
      ∀ argument, argument ∈ right ->
        argument.name ∈ left.map Argument.name := by
  intro hequivalent argument hmem
  rcases hequivalent.2 argument hmem with
    ⟨matched, hmatchedMem, hmatchedEquivalent⟩
  exact List.mem_map.mpr
    ⟨matched, hmatchedMem, hmatchedEquivalent.1⟩

theorem argumentsEquivalent_nil_left
    {right : List Argument} :
    Argument.argumentsEquivalent [] right -> right = [] := by
  intro hequivalent
  cases right with
  | nil =>
      rfl
  | cons argument rest =>
      rcases hequivalent.2 argument (by simp) with
        ⟨matched, hmatchedMem, _hmatchedEquivalent⟩
      simp at hmatchedMem

theorem argumentsEquivalent_nil_right
    {left : List Argument} :
    Argument.argumentsEquivalent left [] -> left = [] := by
  intro hequivalent
  cases left with
  | nil =>
      rfl
  | cons argument rest =>
      rcases hequivalent.1 argument (by simp) with
        ⟨matched, hmatchedMem, _hmatchedEquivalent⟩
      simp at hmatchedMem

theorem eq_of_mem_of_name_eq_of_names_nodup :
    ∀ {arguments : List Argument} {left right : Argument},
      (arguments.map Argument.name).Nodup ->
        left ∈ arguments ->
          right ∈ arguments ->
            left.name = right.name ->
              left = right
  | [], left, _right, _hnodup, hleftMem, _hrightMem, _hname => by
      simp at hleftMem
  | head :: rest, left, right, hnodup, hleftMem, hrightMem, hname => by
      simp at hleftMem hrightMem
      simp at hnodup
      rcases hleftMem with hleft | hleft
      · subst left
        rcases hrightMem with hright | hright
        · subst right
          rfl
        · exact False.elim ((hnodup.1 right hright) hname.symm)
      · rcases hrightMem with hright | hright
        · subst right
          exact False.elim ((hnodup.1 left hleft) hname)
        · exact eq_of_mem_of_name_eq_of_names_nodup hnodup.2 hleft
            hright hname

theorem name_ne_middle_of_names_nodup
    (before suffix : List Argument) (matched candidate : Argument) :
    ((before ++ matched :: suffix).map Argument.name).Nodup ->
      candidate ∈ before ++ suffix ->
        candidate.name ≠ matched.name := by
  induction before with
  | nil =>
      intro hnodup hcandidateMem
      simp at hnodup hcandidateMem
      exact hnodup.1 candidate hcandidateMem
  | cons head before ih =>
      intro hnodup hcandidateMem
      simp at hnodup hcandidateMem
      rcases hcandidateMem with hcandidate | hcandidate
      · subst candidate
        intro hname
        exact hnodup.1.2.1 hname
      · have htailNodup :
          ((before ++ matched :: suffix).map Argument.name).Nodup := by
          simpa using hnodup.2
        exact ih htailNodup (by simpa [List.mem_append] using hcandidate)

theorem argumentsEquivalent_cons_remove_middle
    {head matched : Argument} {leftRest before suffix : List Argument} :
    ((head :: leftRest).map Argument.name).Nodup ->
      ((before ++ matched :: suffix).map Argument.name).Nodup ->
        head.equivalent matched ->
          Argument.argumentsEquivalent (head :: leftRest)
            (before ++ matched :: suffix) ->
            Argument.argumentsEquivalent leftRest (before ++ suffix) := by
  intro hleftNodup hrightNodup hmatched hequivalent
  have hleftParts := hleftNodup
  simp at hleftParts
  constructor
  · intro argument hargumentMem
    rcases hequivalent.1 argument (by simp [hargumentMem]) with
      ⟨candidate, hcandidateMem, hcandidateEquivalent⟩
    have hcandidateSplit :
        candidate ∈ before ∨ candidate = matched ∨ candidate ∈ suffix := by
      simpa [List.mem_append] using hcandidateMem
    rcases hcandidateSplit with hbefore | hmiddle | hsuffix
    · exact ⟨candidate, by simp [List.mem_append, hbefore],
        hcandidateEquivalent⟩
    · subst candidate
      have hargumentNameNeHead : argument.name ≠ head.name :=
        hleftParts.1 argument hargumentMem
      have hargumentNameEqHead : argument.name = head.name :=
        hcandidateEquivalent.1.trans hmatched.1.symm
      exact False.elim (hargumentNameNeHead hargumentNameEqHead)
    · exact ⟨candidate, by simp [List.mem_append, hsuffix],
        hcandidateEquivalent⟩
  · intro argument hargumentMem
    have hargumentMemRight :
        argument ∈ before ++ matched :: suffix := by
      have hsplit : argument ∈ before ∨ argument ∈ suffix := by
        simpa [List.mem_append] using hargumentMem
      rcases hsplit with hbefore | hsuffix
      · simp [List.mem_append, hbefore]
      · simp [List.mem_append, hsuffix]
    rcases hequivalent.2 argument hargumentMemRight with
      ⟨candidate, hcandidateMem, hcandidateEquivalent⟩
    simp at hcandidateMem
    rcases hcandidateMem with hcandidate | hcandidate
    · subst candidate
      have hargumentNameNeMatched :
          argument.name ≠ matched.name :=
        name_ne_middle_of_names_nodup before suffix matched argument
          hrightNodup hargumentMem
      have hargumentNameEqMatched : argument.name = matched.name :=
        hcandidateEquivalent.1.symm.trans hmatched.1
      exact False.elim (hargumentNameNeMatched hargumentNameEqMatched)
    · exact ⟨candidate, hcandidate, hcandidateEquivalent⟩

theorem names_nodup_remove_middle :
    ∀ (before suffix : List Argument) (matched : Argument),
      ((before ++ matched :: suffix).map Argument.name).Nodup ->
        ((before ++ suffix).map Argument.name).Nodup
  | [], suffix, _matched, hnodup => by
      simp at hnodup ⊢
      exact hnodup.2
  | head :: before, suffix, matched, hnodup => by
      simp at hnodup ⊢
      constructor
      · exact ⟨hnodup.1.1, hnodup.1.2.2⟩
      · have htailNodup :
            ((before ++ matched :: suffix).map Argument.name).Nodup := by
          simpa using hnodup.2
        simpa using
          names_nodup_remove_middle before suffix matched htailNodup

inductive EquivalentAlignment : List Argument -> List Argument -> Prop where
  | nil : EquivalentAlignment [] []
  | consMiddle {head matched : Argument} {leftRest before suffix : List Argument} :
      head.equivalent matched ->
        EquivalentAlignment leftRest (before ++ suffix) ->
          EquivalentAlignment (head :: leftRest) (before ++ matched :: suffix)

theorem equivalentAlignment_of_argumentsEquivalent_names_nodup
    (left : List Argument) :
    ∀ right : List Argument,
      (left.map Argument.name).Nodup ->
        (right.map Argument.name).Nodup ->
          Argument.argumentsEquivalent left right ->
            EquivalentAlignment left right := by
  induction left with
  | nil =>
      intro right _hleftNodup _hrightNodup hequivalent
      have hright : right = [] :=
        argumentsEquivalent_nil_left hequivalent
      subst right
      exact EquivalentAlignment.nil
  | cons head leftRest ih =>
      intro right hleftNodup hrightNodup hequivalent
      rcases hequivalent.1 head (by simp) with
        ⟨matched, hmatchedMem, hmatchedEquivalent⟩
      rcases List.mem_iff_append.mp hmatchedMem with
        ⟨before, suffix, hrightEq⟩
      subst right
      have hleftParts := hleftNodup
      simp at hleftParts
      have hrightRestNodup :
          ((before ++ suffix).map Argument.name).Nodup :=
        names_nodup_remove_middle before suffix matched hrightNodup
      have hrestEquivalent :
          Argument.argumentsEquivalent leftRest (before ++ suffix) :=
        argumentsEquivalent_cons_remove_middle hleftNodup hrightNodup
          hmatchedEquivalent hequivalent
      exact EquivalentAlignment.consMiddle hmatchedEquivalent
        (ih (before ++ suffix) hleftParts.2 hrightRestNodup
          hrestEquivalent)

def EquivalentAlignmentImpliesFieldAccessEqBool : Prop :=
  ∀ left right : List Argument,
    EquivalentAlignment left right ->
      FieldAccess.argumentsEqBool left right = true

def ValidEquivalentAlignmentImpliesFieldAccessEqBool : Prop :=
  ∀ left right : List Argument,
    (left.map Argument.name).Nodup ->
      (right.map Argument.name).Nodup ->
        EquivalentAlignment left right ->
          FieldAccess.argumentsEqBool left right = true

theorem fieldAccessEqBool_of_argumentsEquivalent_names_nodup
    (halignment : EquivalentAlignmentImpliesFieldAccessEqBool)
    (left right : List Argument) :
    (left.map Argument.name).Nodup ->
      (right.map Argument.name).Nodup ->
        Argument.argumentsEquivalent left right ->
          FieldAccess.argumentsEqBool left right = true := by
  intro hleftNodup hrightNodup hequivalent
  exact halignment left right
    (equivalentAlignment_of_argumentsEquivalent_names_nodup left right
      hleftNodup hrightNodup hequivalent)

theorem fieldAccessEqBool_of_argumentsEquivalent_names_nodup_valid
    (halignment : ValidEquivalentAlignmentImpliesFieldAccessEqBool)
    (left right : List Argument) :
    (left.map Argument.name).Nodup ->
      (right.map Argument.name).Nodup ->
        Argument.argumentsEquivalent left right ->
          FieldAccess.argumentsEqBool left right = true := by
  intro hleftNodup hrightNodup hequivalent
  exact halignment left right hleftNodup hrightNodup
    (equivalentAlignment_of_argumentsEquivalent_names_nodup left right
      hleftNodup hrightNodup hequivalent)

theorem fieldAccessEqBool_of_validEquivalentAlignment :
    ValidEquivalentAlignmentImpliesFieldAccessEqBool := by
  intro left right hleftNodup hrightNodup halignment
  induction halignment with
  | nil =>
      simp [FieldAccess.argumentsEqBool, FieldAccess.canonicalArguments,
        FieldAccess.sortArgumentsByName, FieldAccess.argumentsEqBoolOrdered]
  | consMiddle hmatched hrestAlignment ih =>
      rename_i head matched leftRest before suffix
      have hleftParts := hleftNodup
      simp at hleftParts
      have hrightRestNodup :
          ((before ++ suffix).map Argument.name).Nodup :=
        names_nodup_remove_middle before suffix matched hrightNodup
      have hrestBool :
          FieldAccess.argumentsEqBool leftRest (before ++ suffix) = true :=
        ih hleftParts.2 hrightRestNodup
      have hrestOrdered :
          FieldAccess.argumentsEqBoolOrdered
              (FieldAccess.sortArgumentsByName
                (FieldAccess.canonicalArguments leftRest))
              (FieldAccess.sortArgumentsByName
                (FieldAccess.canonicalArguments before ++
                  FieldAccess.canonicalArguments suffix)) = true := by
        unfold FieldAccess.argumentsEqBool at hrestBool
        simpa [FieldAccess.canonicalArguments_append] using hrestBool
      have hmatchedNotMem :
          (FieldAccess.canonicalArgument matched).name ∉
            (FieldAccess.canonicalArguments before ++
              FieldAccess.canonicalArguments suffix).map Argument.name := by
        intro hmem
        have hmemOriginal : matched.name ∈ (before ++ suffix).map Argument.name := by
          simpa [FieldAccess.canonicalArgument,
            FieldAccess.canonicalArguments_names, List.map_append] using hmem
        rcases List.mem_map.mp hmemOriginal with
          ⟨candidate, hcandidateMem, hcandidateName⟩
        exact name_ne_middle_of_names_nodup before suffix matched candidate
          hrightNodup hcandidateMem hcandidateName
      have hrightSort :
          FieldAccess.sortArgumentsByName
              (FieldAccess.canonicalArguments (before ++ matched :: suffix)) =
            FieldAccess.insertArgumentSorted
              (FieldAccess.canonicalArgument matched)
              (FieldAccess.sortArgumentsByName
                (FieldAccess.canonicalArguments before ++
                  FieldAccess.canonicalArguments suffix)) := by
        rw [FieldAccess.canonicalArguments_append]
        simp [FieldAccess.canonicalArguments]
        exact FieldAccess.sortArgumentsByName_middle_eq_insert_of_name_not_mem
          (FieldAccess.canonicalArguments before)
          (FieldAccess.canonicalArguments suffix)
          (FieldAccess.canonicalArgument matched)
          hmatchedNotMem
      unfold FieldAccess.argumentsEqBool
      simp [FieldAccess.canonicalArguments, FieldAccess.sortArgumentsByName,
        hrightSort]
      exact FieldAccess.argumentsEqBoolOrdered_insertArgumentSorted
        (FieldAccess.argumentEqBool_canonicalArgument_of_equivalent hmatched)
        hrestOrdered

end Argument

end DataModel

end GraphQL

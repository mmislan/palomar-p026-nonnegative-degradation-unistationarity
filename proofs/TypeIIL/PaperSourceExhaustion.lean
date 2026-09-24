import proofs.TypeIIL.PaperSourceLift

namespace TypeIIL

open TypeII3

/-!
The weak inequalities in the paper are encoded by a Boolean word: `true`
means that the open stem from fork `j` to the next back target contains at
least one nonfork species; `false` is the literal coincidence
`i_j = sigma_(j+1)`.  Long stems and return paths contract to this split-graph
skeleton without changing `(Top)`.
-/

def PaperWeakStemSpecies {l : ℕ} (gap : Fin l → Bool) :=
  Fin l ⊕ {j : Fin l // gap j = true}

noncomputable instance paperWeakStemSubtypeFintype {l : ℕ}
    (gap : Fin l → Bool) : Fintype {j : Fin l // gap j = true} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance paperWeakStemSpeciesFintype {l : ℕ}
    (gap : Fin l → Bool) : Fintype (PaperWeakStemSpecies gap) := by
  unfold PaperWeakStemSpecies
  infer_instance

noncomputable instance paperWeakStemSpeciesDecidableEq {l : ℕ}
    (gap : Fin l → Bool) : DecidableEq (PaperWeakStemSpecies gap) :=
  Classical.decEq _

namespace PaperWeakStemSpecies

variable {l : ℕ} (gap : Fin l → Bool)

def fork (j : Fin l) : PaperWeakStemSpecies gap := Sum.inl j

/-- The back target `sigma_(j+1)` at the end of the stem leaving fork `j`.
For a coincident stem this is the fork itself. -/
noncomputable def stemEnd (j : Fin l) : PaperWeakStemSpecies gap :=
  if h : gap j = true then Sum.inr ⟨j, h⟩ else Sum.inl j

/-- Target of the main-cycle product after contracting the return path. -/
noncomputable def mainNext : PaperWeakStemSpecies gap → PaperWeakStemSpecies gap
  | Sum.inl j =>
      if gap j = true then stemEnd gap j else fork gap (finRotate l j)
  | Sum.inr j => fork gap (finRotate l j.1)

/-- Coefficient-one back product of the fork reaction at `j`. -/
noncomputable def backTarget (j : Fin l) : PaperWeakStemSpecies gap :=
  stemEnd gap ((finRotate l).symm j)

/-- Split-graph edges of the source Type `II_l` skeleton. -/
inductive SplitEdge : PaperWeakStemSpecies gap → PaperWeakStemSpecies gap → Prop
  | main (a) : SplitEdge a (mainNext gap a)
  | back (j) : SplitEdge (fork gap j) (backTarget gap j)

def RestrictedEdge (species : Finset (PaperWeakStemSpecies gap))
    (a b : PaperWeakStemSpecies gap) : Prop :=
  a ∈ species ∧ b ∈ species ∧ SplitEdge gap a b

/-- An explicit proper chemostatted restriction satisfying `(Top)`: its
retained split graph is strongly connected and one retained fork reaction
keeps both of its products.  This is exactly the source convention after
removing reactions with all reactants or all products outside. -/
structure ProperTopRestriction where
  species : Finset (PaperWeakStemSpecies gap)
  proper : species ≠ Finset.univ
  stronglyConnected : ∀ {a}, a ∈ species → ∀ {b}, b ∈ species →
    Relation.ReflTransGen (RestrictedEdge gap species) a b
  internalFork : ∃ j,
    fork gap j ∈ species ∧ mainNext gap (fork gap j) ∈ species ∧
      backTarget gap j ∈ species

/-- Source minimality on the weak-stem skeleton: no proper chemostatted
species restriction retains `(Top)`. -/
def SourceMinimal : Prop := ¬ Nonempty (ProperTopRestriction gap)

def AllSeparated : Prop := ∀ j, gap j = true

def AllCoincident : Prop := ∀ j, gap j = false

@[simp] theorem stemEnd_eq_fork_of_false {j : Fin l}
    (hj : gap j = false) : stemEnd gap j = fork gap j := by
  simp [stemEnd, fork, hj]; rfl

@[simp] theorem mainNext_fork_of_false {j : Fin l}
    (hj : gap j = false) :
    mainNext gap (fork gap j) = fork gap (finRotate l j) := by
  simp [mainNext, fork, hj]; rfl

@[simp] theorem backTarget_rotate_of_false {j : Fin l}
    (hj : gap j = false) :
    backTarget gap (finRotate l j) = fork gap j := by
  rw [backTarget, Equiv.symm_apply_apply]
  exact stemEnd_eq_fork_of_false gap hj

@[simp] theorem mainNext_backTarget
    (j : Fin l) : mainNext gap (backTarget gap j) = fork gap j := by
  let k := (finRotate l).symm j
  have hk : finRotate l k = j := Equiv.apply_symm_apply (finRotate l) j
  change mainNext gap (stemEnd gap k) = fork gap j
  unfold stemEnd
  split_ifs with h
  · simp [mainNext, h, hk]
  · simp [mainNext, h, hk]

/-- A single coincidence generates the whole obstruction to source
minimality.  The retained three-vertex star is

`backTarget(j) → fork(j) ⇄ fork(next j)`

and the middle fork also points to `backTarget(j)`, so its reaction remains
one-to-many after chemostatting. -/
noncomputable def coincidenceRestriction
    (hl : 3 ≤ l) (j : Fin l) (hj : gap j = false)
    (hnotExceptional : ¬ (l = 3 ∧ AllCoincident gap)) :
    ProperTopRestriction gap := by
  let A := fork gap j
  let B := fork gap (finRotate l j)
  let T := backTarget gap j
  let X : Finset (PaperWeakStemSpecies gap) := {A, B, T}
  have hA : A ∈ X := by simp [X]
  have hB : B ∈ X := by simp [X]
  have hT : T ∈ X := by simp [X]
  have hAB : RestrictedEdge gap X A B := by
    refine ⟨hA, hB, ?_⟩
    simpa [A, B, mainNext_fork_of_false gap hj] using
      SplitEdge.main (gap := gap) A
  have hAT : RestrictedEdge gap X A T := by
    exact ⟨hA, hT, SplitEdge.back (gap := gap) j⟩
  have hBA : RestrictedEdge gap X B A := by
    refine ⟨hB, hA, ?_⟩
    change SplitEdge gap (fork gap (finRotate l j)) (fork gap j)
    rw [← backTarget_rotate_of_false gap hj]
    exact SplitEdge.back (gap := gap) (finRotate l j)
  have hTA : RestrictedEdge gap X T A := by
    refine ⟨hT, hA, ?_⟩
    simpa [A, T] using SplitEdge.main (gap := gap) T
  have hToA : ∀ {u}, u ∈ X →
      Relation.ReflTransGen (RestrictedEdge gap X) u A := by
    intro u hu
    simp [X] at hu
    rcases hu with rfl | rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single hBA
    · exact Relation.ReflTransGen.single hTA
  have hFromA : ∀ {u}, u ∈ X →
      Relation.ReflTransGen (RestrictedEdge gap X) A u := by
    intro u hu
    simp [X] at hu
    rcases hu with rfl | rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single hAB
    · exact Relation.ReflTransGen.single hAT
  have hproper : X ≠ Finset.univ := by
    intro hX
    have hcardX : X.card ≤ 3 := by
      dsimp [X]
      have h1 := Finset.card_insert_le A {B, T}
      have h2 := Finset.card_insert_le B {T}
      simp only [Finset.card_singleton] at h2
      omega
    have hcardSpecies : Fintype.card (PaperWeakStemSpecies gap) ≤ 3 := by
      rw [← Finset.card_univ, ← hX]
      exact hcardX
    have hcardFormula : Fintype.card (PaperWeakStemSpecies gap) =
        l + Fintype.card {k : Fin l // gap k = true} := by
      change Fintype.card (Fin l ⊕ {k : Fin l // gap k = true}) = _
      simpa only [Fintype.card_fin] using
        (@Fintype.card_sum (Fin l) {k : Fin l // gap k = true}
          inferInstance inferInstance)
    have hcardLarge : 3 < Fintype.card (PaperWeakStemSpecies gap) := by
      rw [hcardFormula]
      by_cases hl3 : l = 3
      · have hnall : ¬ AllCoincident gap := fun hall =>
          hnotExceptional ⟨hl3, hall⟩
        rw [AllCoincident, not_forall] at hnall
        obtain ⟨k, hk⟩ := hnall
        have hktr : gap k = true := by
          cases hkg : gap k
          · exact False.elim (hk hkg)
          · rfl
        have hnonempty : Nonempty {u : Fin l // gap u = true} :=
          ⟨⟨k, hktr⟩⟩
        have hpos : 0 < Fintype.card {u : Fin l // gap u = true} :=
          Fintype.card_pos_iff.mpr hnonempty
        omega
      · omega
    omega
  exact
    { species := X
      proper := hproper
      stronglyConnected := by
        intro a ha b hb
        exact (hToA ha).trans (hFromA hb)
      internalFork := by
        refine ⟨j, hA, ?_, hT⟩
        rw [mainNext_fork_of_false gap hj]
        exact hB }

/-- Exact source-exhaustion theorem for the paper weak ordering.  Minimality
leaves either every stem strictly separated or the fully coincident
three-fork quotient.  No gap word is enumerated. -/
theorem source_exhaustion_of_minimal
    (hl : 3 ≤ l) (hminimal : SourceMinimal gap) :
    AllSeparated gap ∨ (l = 3 ∧ AllCoincident gap) := by
  by_cases hsep : AllSeparated gap
  · exact Or.inl hsep
  right
  by_contra hex
  apply hminimal
  rw [AllSeparated, not_forall] at hsep
  obtain ⟨j, hj⟩ := hsep
  have hjfalse : gap j = false := by
    exact Bool.eq_false_of_not_eq_true hj
  exact ⟨coincidenceRestriction gap hl j hjfalse hex⟩

end PaperWeakStemSpecies

end TypeIIL

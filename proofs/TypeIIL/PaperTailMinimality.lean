module

public import proofs.TypeII3.Network.SourceMembership

@[expose] public section

namespace TypeIIL

open TypeII3
open scoped BigOperators

/-!
The generating source-minimality fact behind the paper Type `II_l` normal
form.  A back branch closes a directed cycle consisting of its return tail.
If any forward edge of that tail replicates, the tail is itself a proper
stoichiometrically autocatalytic restriction.  Thus source minimality forces
the complete return tail to be unit-stoichiometric; arbitrary multiplicities
can survive only on the complementary stem.
-/

/-- Stoichiometric matrix of a directed cycle.  Column `j` consumes species
`j` and produces `weight j` copies of its cyclic successor. -/
def paperTailCycleRestriction {N : ℕ} (weight : Fin N → ℕ) :
    Fin N → Fin N → ℝ :=
  fun i j =>
    (if i = j then -1 else 0) +
      (if i = finRotate N j then (weight j : ℝ) else 0)

/-- A source-minimal paper core must rule out each proper return-tail cycle. -/
def PaperTailPassesMinimality {N : ℕ} (weight : Fin N → ℕ) : Prop :=
  ¬ StoichiometricallyAutocatalytic (paperTailCycleRestriction weight)

/-- The row action of a cyclic restriction has exactly one incoming and one
outgoing reaction. -/
theorem paperTailCycleRestriction_mulVec
    {N : ℕ} [NeZero N] (weight : Fin N → ℕ) (v : Fin N → ℝ)
    (i : Fin N) :
    ∑ j, paperTailCycleRestriction weight i j * v j =
      -v i + weight ((finRotate N).symm i) * v ((finRotate N).symm i) := by
  classical
  simp only [paperTailCycleRestriction, add_mul, Finset.sum_add_distrib]
  have hdiag :
      (∑ j, (if i = j then -1 else 0) * v j) = -v i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      simp [Ne.symm hbi]
    · simp
  have hincoming :
      (∑ j, (if i = finRotate N j then (weight j : ℝ) else 0) * v j) =
        weight ((finRotate N).symm i) * v ((finRotate N).symm i) := by
    rw [Finset.sum_eq_single ((finRotate N).symm i)]
    · simp
    · intro b _ hb
      have hne : i ≠ b + 1 := by
        intro h
        apply hb
        apply (finRotate N).injective
        calc
          finRotate N b = i := by simpa [finRotate_apply] using h.symm
          _ = finRotate N ((finRotate N).symm i) :=
            ((finRotate N).apply_symm_apply i).symm
      simp [hne]
    · simp
  rw [hdiag, hincoming]

/-- Universal positive flux witness for a return-tail cycle, enumerated so
the distinguished replicating edge is reaction zero. -/
def paperTailReplicationWitness (N : ℕ) : Fin N → ℝ :=
  fun j => if j.val = 0 then N + 1 else 2 * (N + 1) - j.val

theorem paperTailReplicationWitness_pos
    {N : ℕ} (hN : 2 ≤ N) (j : Fin N) :
    0 < paperTailReplicationWitness N j := by
  by_cases hj : j.val = 0
  · simp only [paperTailReplicationWitness, ite_eq_left hj]
    positivity
  · simp only [paperTailReplicationWitness, ite_eq_right hj]
    have hjle : (j.val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt j.isLt)
    nlinarith

/-- A directed return-tail cycle containing a replicating edge is itself
stoichiometrically autocatalytic.  The witness is length-independent: after
the gain-two edge its currents descend by one until they close with positive
slack. -/
theorem paper_tail_cycle_autocatalytic_of_zero_replication
    {m : ℕ} (hm : 1 ≤ m) (weight : Fin (m + 1) → ℕ)
    (hw : ∀ j, 0 < weight j) (hrep : 2 ≤ weight 0) :
    StoichiometricallyAutocatalytic (paperTailCycleRestriction weight) := by
  let : NeZero (m + 1) := ⟨by omega⟩
  refine ⟨paperTailReplicationWitness (m + 1),
    paperTailReplicationWitness_pos (by omega), ?_⟩
  intro i
  rw [paperTailCycleRestriction_mulVec]
  let pred : Fin (m + 1) := (finRotate (m + 1)).symm i
  have hpredWeight : (1 : ℝ) ≤ weight pred := by
    exact_mod_cast hw pred
  by_cases hi0 : i = 0
  · subst i
    have hpred : pred = Fin.last m := by
      apply (finRotate (m + 1)).injective
      simp [pred]
    have hm0 : m ≠ 0 := by omega
    have hpredWeightLast : (1 : ℝ) ≤ weight (Fin.last m) := by
      simpa [hpred] using hpredWeight
    rw [show (finRotate (m + 1)).symm (0 : Fin (m + 1)) = pred from rfl,
      hpred]
    simp [paperTailReplicationWitness, hm0]
    have hnonneg : (0 : ℝ) ≤
        2 * ((m + 1 : ℝ) + 1) - (Fin.last m).val := by
      simp only [Fin.val_last]
      have hmR : (0 : ℝ) ≤ m := by positivity
      linarith
    have hmul :
        2 * ((m + 1 : ℝ) + 1) - (Fin.last m).val ≤
          weight (Fin.last m) *
            (2 * ((m + 1 : ℝ) + 1) - (Fin.last m).val) := by
      simpa using mul_le_mul_of_nonneg_right hpredWeightLast hnonneg
    simp only [Fin.val_last] at hmul ⊢
    norm_num at hmul ⊢
    linarith
  · have hipredVal : pred.val = i.val - 1 := by
      exact coe_finRotate_symm_of_ne_zero hi0
    by_cases hi1 : i.val = 1
    · have hpred0 : pred = 0 := by
        apply Fin.ext
        rw [hipredVal, hi1]
        simp
      have hiEq : i = ⟨1, by omega⟩ := by
        apply Fin.ext
        exact hi1
      have hi0val : i.val ≠ 0 := Fin.val_ne_zero_iff.mpr hi0
      rw [show (finRotate (m + 1)).symm i = pred from rfl, hpred0]
      simp [paperTailReplicationWitness, hi0val]
      have hrepR : (2 : ℝ) ≤ weight (0 : Fin (m + 1)) := by
        exact_mod_cast hrep
      have hbaseNonneg : (0 : ℝ) ≤ (m + 1 : ℝ) + 1 := by positivity
      have hmul : (2 : ℝ) * ((m + 1 : ℝ) + 1) ≤
          weight (0 : Fin (m + 1)) * ((m + 1 : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hrepR hbaseNonneg
      rw [hiEq]
      norm_num at hmul ⊢
      linarith
    · have hi0val : i.val ≠ 0 := Fin.val_ne_zero_iff.mpr hi0
      have hipred0 : pred.val ≠ 0 := by rw [hipredVal]; omega
      rw [show (finRotate (m + 1)).symm i = pred from rfl]
      simp only [paperTailReplicationWitness, ite_eq_right hipred0, ite_eq_right hi0val]
      have hpredPos : (0 : ℝ) <
          2 * ((m + 1 : ℝ) + 1) - pred.val := by
        have hpLt : (pred.val : ℝ) < m + 1 := by exact_mod_cast pred.isLt
        nlinarith
      have hmul :
          2 * ((m + 1 : ℝ) + 1) - pred.val ≤
          weight pred * (2 * ((m + 1 : ℝ) + 1) - pred.val) :=
        by simpa using
          mul_le_mul_of_nonneg_right hpredWeight (le_of_lt hpredPos)
      norm_num at hmul ⊢
      norm_num [hipredVal, Nat.cast_sub (by omega : 1 ≤ i.val)] at hmul ⊢
      linarith

/-- Source minimality therefore forces the first edge of an enumerated return
tail to be unit-stoichiometric. -/
theorem paper_tail_zero_weight_eq_one_of_minimality
    {m : ℕ} (hm : 1 ≤ m) (weight : Fin (m + 1) → ℕ)
    (hw : ∀ j, 0 < weight j)
    (hminimal : PaperTailPassesMinimality weight) :
    weight 0 = 1 := by
  by_contra hne
  have hw0 := hw 0
  have hrep : 2 ≤ weight 0 := by omega
  exact hminimal (paper_tail_cycle_autocatalytic_of_zero_replication
    hm weight hw hrep)

/-- Re-enumerate a return subcycle with edge `start` as reaction zero. -/
def paperTailRotatedWeight {N : ℕ} (weight : Fin N → ℕ)
    (start : Fin N) : Fin N → ℕ :=
  fun j => weight (finCycle start j)

/-- Exact source minimality rules out the proper return-tail restriction in
every cyclic enumeration. -/
def EveryPaperTailRotationPassesMinimality {N : ℕ}
    (weight : Fin N → ℕ) : Prop :=
  ∀ start, PaperTailPassesMinimality (paperTailRotatedWeight weight start)

/-- The generating minimality consequence: every multiplier on a proper
return tail is one.  No length induction or list of local patterns occurs;
the proof rotates the single universal positive-flux certificate. -/
theorem paper_tail_all_weights_eq_one_of_minimality
    {m : ℕ} (hm : 1 ≤ m) (weight : Fin (m + 1) → ℕ)
    (hw : ∀ j, 0 < weight j)
    (hminimal : EveryPaperTailRotationPassesMinimality weight) :
    ∀ j, weight j = 1 := by
  intro j
  have hrotPos : ∀ k, 0 < paperTailRotatedWeight weight j k := by
    intro k
    exact hw _
  have hzero := paper_tail_zero_weight_eq_one_of_minimality hm
    (paperTailRotatedWeight weight j) hrotPos (hminimal j)
  simpa [paperTailRotatedWeight, finCycle] using hzero

end TypeIIL

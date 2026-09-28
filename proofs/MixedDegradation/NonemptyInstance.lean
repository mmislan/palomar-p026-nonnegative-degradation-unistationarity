module

public import proofs.MixedDegradation.Main

@[expose] public section

/-!
# A nonempty instance of the Type `II_l` hypothesis class

The Type `II_l` conjunct of `MixedDegradation.paper_mixed_degradation_unistationarity`
quantifies over raw open networks `Q : TypeII.PaperRaw.OpenNetwork l` satisfying
`TypeII.PaperRaw.IsPaperTypeIILCore Q` and `3 ≤ l`, and over positive stationary
states `x : Q.State` (`Q.PositiveState x`, `Q.Stationary x`).

This file exhibits one such network together with a positive stationary state, so
that hypothesis class is demonstrably nonempty.  The network has `l = 3` forks and
six core species: `next i = i + 1` on `Fin 6`, forks `0, 2, 4`, gap species
`1, 3, 5`, the back product of fork `2j` is the preceding gap species `2j - 1`,
every stem is separated (`weakGap ≡ true`), all main weights and tail weights are
`1`, every return chain is the direct unit chain, all reversible rates are `1` and
all degradation constants are `0`.  The state with every concentration equal to
`1` is positive and stationary.
-/

namespace MixedDegradation

namespace NonemptyInstance

open TypeIIL TypeII3
open TypeIIL.SourceCyclicNonemptyGapSystem
open TypeII.PaperRaw

noncomputable section

/-! ## Cyclic gap geometry -/

/-- `i ↦ i + 1` on six core species: forks `0, 2, 4` and gap species `1, 3, 5`. -/
def next6 : Fin 6 ≃ Fin 6 where
  toFun i := i + 1
  invFun i := i - 1
  left_inv := by decide
  right_inv := by decide

/-- Coefficient-one back product of each fork: the preceding gap species. -/
def back6 : Fin 6 → Option (Fin 6) := ![some 5, none, some 1, none, some 3, none]

/-- The fork successor on the three forks. -/
def step3 : Fin 3 ≃ Fin 3 where
  toFun j := j + 1
  invFun j := j - 1
  left_inv := by decide
  right_inv := by decide

/-- Fork `j` is the core species `2j`. -/
def forkEmb : Fin 3 ↪ Fin 6 := ⟨![0, 2, 4], by decide⟩

/-- The one-species gap after fork `j` is the core species `2j + 1`. -/
def gapEmb (j : Fin 3) : SourceGapEmbedding next6 back6 0 where
  idx := ⟨fun _ => ![1, 3, 5] j, fun a b _ => Fin.ext (by have := a.isLt; have := b.isLt; omega)⟩
  nonfork := by fin_cases j <;> decide
  successor_support := by fin_cases j <;> decide
  predecessor_support := by fin_cases j <;> decide
  no_two_cycle := by decide

/-- The cyclic nonempty-gap system with three forks and three one-species gaps. -/
def src6 : SourceCyclicNonemptyGapSystem (l := 3) next6 back6 where
  step := step3
  cyclicOrder := Equiv.refl _
  step_cyclicOrder := by decide
  fork := forkEmb
  gapLength := fun _ => 0
  gap := gapEmb
  wrap := fun j =>
    { pre :=
        { terminal_next := by fin_cases j <;> decide
          fork_back := by fin_cases j <;> decide
          fork_successor_outside := by fin_cases j <;> decide
          fork_ne_next := by fin_cases j <;> decide }
      post :=
        { first_eq := by fin_cases j <;> decide
          fork_back := by fin_cases j <;> decide
          fork_outside := by fin_cases j <;> decide
          fork_not_successor := by fin_cases j <;> decide
          back_outside := by fin_cases j <;> decide
          back_not_successor := by fin_cases j <;> decide }
      right_successor_ne_left := by fin_cases j <;> decide
      right_successor_ne_leftBack := by fin_cases j <;> decide
      right_ne_leftBack := by fin_cases j <;> decide }
  cover := by decide
  fork_ne_gap := by decide
  gap_owner := by decide

/-! ## Kinetics and the positive stationary state -/

/-- Unit main weights. -/
def weight6 : Fin 6 → ℕ := fun _ => 1

/-- All rates `1`, unit tail weights, direct unit return chains, zero degradation. -/
def rates6 : TypeII.Rates src6 weight6 where
  tailDepth := fun _ => 1
  tailDepth_pos := fun _ => le_rfl
  tailCycleWeight := fun _ _ => 1
  tailCycleWeight_pos := fun _ _ => Nat.one_pos
  terminal_cycle_weight := fun _ => rfl
  chain := fun _ => UnitChain.direct 1 1 one_pos one_pos
  plus := fun _ => 1
  minus := fun _ => 1
  degrade := fun _ => 0
  plus_pos := fun _ => one_pos
  minus_pos := fun _ => one_pos
  degrade_nonneg := fun _ => le_rfl
  terminal_plus := fun _ => rfl
  terminal_minus := fun _ => rfl

/-- Every concentration equal to `1`. -/
def x6 : TypeII.State src6 weight6 rates6 where
  core := fun _ => 1
  tail := fun _ => PUnit.unit

theorem x6_positive : TypeII.Positive x6 :=
  ⟨fun _ => one_pos, fun _ => trivial⟩

theorem x6_stationary : TypeII.Stationary rates6 x6 := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => ?_, fun _ => ?_⟩
  · show (0 : ℝ) = 1 * 1 - 1 * 1 ∧ (0 : ℝ) = 1 * 1 - 1 * 1
    norm_num
  · simp [TypeII.current, paperSourceProductMonomial,
      paperTailBoundaryContribution, rates6, x6]

/-- The separated kinetic realization. -/
def sep3 : SeparatedRealization 3 where
  n := 6
  next := next6
  back := back6
  source := src6
  weight := weight6
  weight_pos := fun _ => Nat.one_pos
  rates := rates6

/-- Inert coincident record (never selected, since every stem is separated). -/
def coin : Coincident.AllZeroParams where
  plus0 := 1
  plus1 := 1
  plus2 := 1
  minus0 := 1
  minus1 := 1
  minus2 := 1
  d0 := 0
  d1 := 0
  d2 := 0
  m0 := 1
  m1 := 1
  m2 := 1
  plus0_pos := one_pos
  plus1_pos := one_pos
  plus2_pos := one_pos
  minus0_pos := one_pos
  minus1_pos := one_pos
  minus2_pos := one_pos
  d0_nonneg := le_rfl
  d1_nonneg := le_rfl
  d2_nonneg := le_rfl
  m0_pos := Nat.one_pos
  m1_pos := Nat.one_pos
  m2_pos := Nat.one_pos

/-- Every stem is separated. -/
def gap3 : Fin 3 → Bool := fun _ => true

theorem gap3_apply (k : Fin 3) : gap3 k = true := rfl

/-- The raw open network. -/
def Q3 : OpenNetwork 3 where
  weakGap := gap3
  separated := sep3
  coincident := coin

theorem Q3_allSeparated : PaperWeakStemSpecies.AllSeparated Q3.weakGap :=
  fun _ => rfl

theorem positiveState_of_separated {l : ℕ} (Q : OpenNetwork l)
    (hsep : PaperWeakStemSpecies.AllSeparated Q.weakGap) (y : Q.separated.State)
    (hy : Q.separated.Positive y) :
    Q.PositiveState ((Q.separatedStateEquiv hsep).symm y) := by
  rw [OpenNetwork.PositiveState, dite_eq_left_of_eq_true (eq_true hsep)]
  show Q.separated.Positive (Q.separatedStateEquiv hsep ((Q.separatedStateEquiv hsep).symm y))
  rw [Equiv.apply_symm_apply]
  exact hy

theorem stationary_of_separated {l : ℕ} (Q : OpenNetwork l)
    (hsep : PaperWeakStemSpecies.AllSeparated Q.weakGap) (y : Q.separated.State)
    (hy : Q.separated.Stationary y) :
    Q.Stationary ((Q.separatedStateEquiv hsep).symm y) := by
  rw [OpenNetwork.Stationary, dite_eq_left_of_eq_true (eq_true hsep)]
  show Q.separated.Stationary (Q.separatedStateEquiv hsep ((Q.separatedStateEquiv hsep).symm y))
  rw [Equiv.apply_symm_apply]
  exact hy

theorem Q3_positive_stationary :
    ∃ x : Q3.State, Q3.PositiveState x ∧ Q3.Stationary x :=
  ⟨(Q3.separatedStateEquiv Q3_allSeparated).symm x6,
    positiveState_of_separated Q3 Q3_allSeparated x6 x6_positive,
    stationary_of_separated Q3 Q3_allSeparated x6 x6_stationary⟩

/-! ## The weak-stem skeleton and `(Top)` -/

theorem rot_val (k : Fin 3) : (finRotate 3 k).val = (k.val + 1) % 3 := by
  fin_cases k <;> decide

theorem mainNext_inl (k : Fin 3) :
    PaperWeakStemSpecies.mainNext gap3 (Sum.inl k) = Sum.inr ⟨k, gap3_apply k⟩ := rfl

theorem mainNext_inr (k : {k : Fin 3 // gap3 k = true}) :
    PaperWeakStemSpecies.mainNext gap3 (Sum.inr k) = Sum.inl (finRotate 3 k.1) := rfl

theorem backTarget_eq (k : Fin 3) :
    PaperWeakStemSpecies.backTarget gap3 k =
      Sum.inr ⟨(finRotate 3).symm k, gap3_apply _⟩ := rfl

/-- A single main edge of the full (unrestricted) split graph. -/
theorem main_step (a : PaperWeakStemSpecies gap3) :
    Relation.ReflTransGen (PaperWeakStemSpecies.RestrictedEdge gap3 Finset.univ) a
      (PaperWeakStemSpecies.mainNext gap3 a) :=
  Relation.ReflTransGen.single
    ⟨Finset.mem_univ _, Finset.mem_univ _, PaperWeakStemSpecies.SplitEdge.main a⟩

theorem fork_step (k : Fin 3) :
    Relation.ReflTransGen (PaperWeakStemSpecies.RestrictedEdge gap3 Finset.univ)
      (Sum.inl k) (Sum.inl (finRotate 3 k)) := by
  have h1 := main_step (Sum.inl k)
  rw [mainNext_inl] at h1
  have h2 := main_step (Sum.inr ⟨k, gap3_apply k⟩)
  rw [mainNext_inr] at h2
  exact h1.trans h2

theorem fork_reach (k m : Fin 3) :
    Relation.ReflTransGen (PaperWeakStemSpecies.RestrictedEdge gap3 Finset.univ)
      (Sum.inl k) (Sum.inl m) := by
  have e1 := rot_val k
  have e2 := rot_val (finRotate 3 k)
  have hk := k.isLt
  have hm := m.isLt
  rcases (by omega : m.val = k.val ∨ m.val = (finRotate 3 k).val ∨
      m.val = (finRotate 3 (finRotate 3 k)).val) with h | h | h
  · obtain rfl : m = k := Fin.ext h
    exact Relation.ReflTransGen.refl
  · obtain rfl : m = finRotate 3 k := Fin.ext h
    exact fork_step k
  · obtain rfl : m = finRotate 3 (finRotate 3 k) := Fin.ext h
    exact (fork_step k).trans (fork_step _)

theorem sourceTop_gap3 : SourceTop gap3 where
  stronglyConnected := by
    intro a b
    have ha : Relation.ReflTransGen
        (PaperWeakStemSpecies.RestrictedEdge gap3 Finset.univ) a (Sum.inl 0) := by
      rcases a with k | k
      · exact fork_reach k 0
      · have h := main_step (Sum.inr k)
        rw [mainNext_inr] at h
        exact h.trans (fork_reach _ 0)
    have hb : Relation.ReflTransGen
        (PaperWeakStemSpecies.RestrictedEdge gap3 Finset.univ) (Sum.inl 0) b := by
      rcases b with k | k
      · exact fork_reach 0 k
      · have h := main_step (Sum.inl k.1)
        rw [mainNext_inl] at h
        exact (fork_reach 0 k.1).trans h
    exact ha.trans hb
  internalFork := ⟨0, Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _⟩

/-! ## Stem minimality

Positions along the main cycle, starting at the stem end `inr j` of the internal
fork `j` and ending at the fork `inl j`: main edges raise the position by one
except for the wrap to position `0`, and back edges lower it. -/

/-- Cycle position relative to fork `j`. -/
def pos (j : Fin 3) : Fin 3 ⊕ {k : Fin 3 // gap3 k = true} → ℕ
  | Sum.inl k => 2 * ((k.val + 2 - j.val) % 3) + 1
  | Sum.inr k => 2 * ((k.1.val + 3 - j.val) % 3)

theorem pos_le (j : Fin 3) (v : PaperWeakStemSpecies gap3) : pos j v ≤ 5 := by
  rcases v with k | k
  · show 2 * ((k.val + 2 - j.val) % 3) + 1 ≤ 5
    omega
  · show 2 * ((k.1.val + 3 - j.val) % 3) ≤ 5
    omega

theorem pos_inj (j : Fin 3) {v w : PaperWeakStemSpecies gap3}
    (h : pos j v = pos j w) : v = w := by
  have hj := j.isLt
  rcases v with k | ⟨k, hk⟩ <;> rcases w with k' | ⟨k', hk'⟩
  · have hkl := k.isLt
    have hkl' := k'.isLt
    have h' : 2 * ((k.val + 2 - j.val) % 3) + 1 =
        2 * ((k'.val + 2 - j.val) % 3) + 1 := h
    have : k = k' := Fin.ext (by omega)
    rw [this]
  · have h' : 2 * ((k.val + 2 - j.val) % 3) + 1 = 2 * ((k'.val + 3 - j.val) % 3) := h
    omega
  · have h' : 2 * ((k.val + 3 - j.val) % 3) = 2 * ((k'.val + 2 - j.val) % 3) + 1 := h
    omega
  · have hkl := k.isLt
    have hkl' := k'.isLt
    have h' : 2 * ((k.val + 3 - j.val) % 3) = 2 * ((k'.val + 3 - j.val) % 3) := h
    have : k = k' := Fin.ext (by omega)
    subst this
    rfl

theorem pos_edge (j : Fin 3) {a b : PaperWeakStemSpecies gap3}
    (h : PaperWeakStemSpecies.SplitEdge gap3 a b) :
    pos j b < pos j a ∨ pos j b = pos j a + 1 ∨ pos j b = 0 := by
  have hj := j.isLt
  cases h with
  | main a =>
      rcases a with k | k
      · rw [mainNext_inl]
        have hk := k.isLt
        show 2 * ((k.val + 3 - j.val) % 3) < 2 * ((k.val + 2 - j.val) % 3) + 1 ∨
          2 * ((k.val + 3 - j.val) % 3) = 2 * ((k.val + 2 - j.val) % 3) + 1 + 1 ∨
          2 * ((k.val + 3 - j.val) % 3) = 0
        omega
      · rw [mainNext_inr]
        have hk := k.1.isLt
        have hr := rot_val k.1
        show 2 * (((finRotate 3 k.1).val + 2 - j.val) % 3) + 1 <
            2 * ((k.1.val + 3 - j.val) % 3) ∨
          2 * (((finRotate 3 k.1).val + 2 - j.val) % 3) + 1 =
            2 * ((k.1.val + 3 - j.val) % 3) + 1 ∨
          2 * (((finRotate 3 k.1).val + 2 - j.val) % 3) + 1 = 0
        omega
  | back k =>
      rw [backTarget_eq]
      have hm := ((finRotate 3).symm k).isLt
      have hr := rot_val ((finRotate 3).symm k)
      rw [Equiv.apply_symm_apply] at hr
      show 2 * ((((finRotate 3).symm k).val + 3 - j.val) % 3) <
          2 * ((k.val + 2 - j.val) % 3) + 1 ∨
        2 * ((((finRotate 3).symm k).val + 3 - j.val) % 3) =
          2 * ((k.val + 2 - j.val) % 3) + 1 + 1 ∨
        2 * ((((finRotate 3).symm k).val + 3 - j.val) % 3) = 0
      omega

theorem not_properTop (R : PaperWeakStemSpecies.ProperTopRestriction gap3) : False := by
  obtain ⟨j, hfork, hnext, _⟩ := R.internalFork
  rw [PaperWeakStemSpecies.fork, mainNext_inl] at hnext
  have hpath := R.stronglyConnected hnext hfork
  have key : ∀ b, Relation.ReflTransGen
      (PaperWeakStemSpecies.RestrictedEdge gap3 R.species)
      (Sum.inr ⟨j, gap3_apply j⟩) b →
      ∀ v, pos j v ≤ pos j b → v ∈ R.species := by
    intro b hb
    induction hb with
    | refl =>
        intro v hv
        have h0 : pos j (Sum.inr ⟨j, gap3_apply j⟩) = 0 := by
          show 2 * ((j.val + 3 - j.val) % 3) = 0
          omega
        rw [pos_inj j (by omega : pos j v = pos j (Sum.inr ⟨j, gap3_apply j⟩))]
        exact hnext
    | @tail _ c _ hbc ih =>
        obtain ⟨_, hc, he⟩ := hbc
        intro v hv
        rcases pos_edge j he with h | h | h
        · exact ih v (by omega)
        · by_cases hvc : pos j v = pos j c
          · rw [pos_inj j hvc]
            exact hc
          · exact ih v (by omega)
        · rw [pos_inj j (by omega : pos j v = pos j c)]
          exact hc
  have hall : ∀ v, v ∈ R.species := by
    intro v
    have h5 : pos j (Sum.inl j) = 5 := by
      show 2 * ((j.val + 2 - j.val) % 3) + 1 = 5
      omega
    exact key _ hpath v ((pos_le j v).trans_eq h5.symm)
  exact R.proper (Finset.eq_univ_iff_forall.mpr hall)

/-! ## Tail minimality -/

/-- With unit weights the tail-cycle restriction has zero column sums, so it is
not stoichiometrically autocatalytic. -/
theorem unit_tail_not_autocatalytic (N : ℕ) :
    ¬ StoichiometricallyAutocatalytic
      (paperTailCycleRestriction (fun _ : Fin (N + 1) => 1)) := by
  rintro ⟨v, _, hrow⟩
  have hzero : ∑ i, ∑ j, paperTailCycleRestriction (fun _ : Fin (N + 1) => 1) i j * v j
      = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_mul]
    simp [paperTailCycleRestriction, Finset.sum_add_distrib]
  have hpos : 0 < ∑ i, ∑ j,
      paperTailCycleRestriction (fun _ : Fin (N + 1) => 1) i j * v j :=
    Finset.sum_pos (fun i _ => hrow i) Finset.univ_nonempty
  exact lt_irrefl _ (hzero ▸ hpos)

theorem Q3_sourceMinimal : SourceMinimal Q3 := by
  rintro ⟨R⟩
  cases R with
  | stem R => exact not_properTop R
  | tail _ j _ hauto =>
      exact unit_tail_not_autocatalytic (Q3.separated.rates.tailDepth j) hauto

theorem Q3_core : IsPaperTypeIILCore Q3 where
  top := sourceTop_gap3
  minimal := Q3_sourceMinimal

end

end NonemptyInstance

open TypeII.PaperRaw in
/-- **Nonemptiness of the Type `II_l` hypothesis class.** There is a raw open
network satisfying exactly the hypotheses of the Type `II_l` conjunct of
`paper_mixed_degradation_unistationarity` (`IsPaperTypeIILCore Q` and `3 ≤ l`)
that has a positive stationary state (`Q.PositiveState x ∧ Q.Stationary x`). -/
theorem paper_typeIIL_instance_nonempty :
    ∃ (l : ℕ) (Q : OpenNetwork l),
      IsPaperTypeIILCore Q ∧ 3 ≤ l ∧
      ∃ x : Q.State, Q.PositiveState x ∧ Q.Stationary x :=
  ⟨3, NonemptyInstance.Q3, NonemptyInstance.Q3_core, le_rfl,
    NonemptyInstance.Q3_positive_stationary⟩

open TypeII.PaperRaw in
/-- Applying the selected theorem to the instance: its positive stationary state
exists and is unique. -/
theorem paper_typeIIL_instance_unique :
    ∃ (l : ℕ) (Q : OpenNetwork l),
      IsPaperTypeIILCore Q ∧ 3 ≤ l ∧
      ∃! x : Q.State, Q.PositiveState x ∧ Q.Stationary x := by
  obtain ⟨l, Q, hcore, hl, x, hx, hxs⟩ := paper_typeIIL_instance_nonempty
  exact ⟨l, Q, hcore, hl, x, ⟨hx, hxs⟩, fun y hy =>
    paper_mixed_degradation_unistationarity.1 l Q hcore hl y x hy.1 hx hy.2 hxs⟩

end MixedDegradation

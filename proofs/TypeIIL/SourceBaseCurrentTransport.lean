import proofs.TypeIIL.SourceForkRowAssembly
import proofs.TypeIIL.PaperCurrentTransport
import proofs.TypeII3.Network.TwoRootKernel

namespace TypeIIL

open scoped BigOperators

/-- Universal discrete-divergence formula for a weighted source cycle.  The
only incoming cycle current at species `i` is the current of `next⁻¹(i)`;
all remaining incoming currents are precisely the fork back branches. -/
theorem sourceStoich_mul_current_eq_divergence
    {n : ℕ} (next : Fin n ≃ Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) (J : Fin n → ℝ) (i : Fin n) :
    (∑ k, sourceStoich next weight back i k * J k) =
      (weight (next.symm i) : ℝ) * J (next.symm i) - J i +
        ∑ k, match back k with
          | none => 0
          | some z => if i = z then J k else 0 := by
  classical
  have hpoint : ∀ k : Fin n,
      sourceStoich next weight back i k * J k =
        (if i = next k then (weight k : ℝ) * J k else 0) +
          (match back k with
            | none => 0
            | some z => if i = z then J k else 0) -
          (if i = k then J k else 0) := by
    intro k
    cases h : back k with
    | none =>
        simp only [sourceStoich, sourceProductExponent, h]
        split_ifs <;> ring
    | some z =>
        simp only [sourceStoich, sourceProductExponent, h]
        split_ifs <;> norm_num [Nat.cast_add] <;> ring
  have hsucc :
      (∑ k, if i = next k then (weight k : ℝ) * J k else 0) =
        (weight (next.symm i) : ℝ) * J (next.symm i) := by
    rw [Fintype.sum_eq_single (next.symm i)]
    · simp
    · intro b hb
      have hne : i ≠ next b := by
        intro h
        apply hb
        apply next.injective
        simpa using h.symm
      simp [hne]
  have hself : (∑ k, if i = k then J k else 0) = J i := by simp
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsucc, hself]
  ring

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

/-- No source back branch targets a fork.  This is a global incidence
consequence of the fork/gap partition, independent of all rates and states. -/
theorem fork_ne_back_target
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (j : Fin l) {k z : Fin n} (hk : back k = some z) :
    S.fork j ≠ z := by
  rcases S.cover k with ⟨b, rfl⟩ | ⟨a, i, rfl⟩
  · rw [S.back_fork b] at hk
    injection hk with hk
    subst z
    exact (S.gap_point_ne_fork j (S.step.symm b)
      (Fin.last (S.gapLength (S.step.symm b)))).symm
  · rw [(S.gap a).nonfork i] at hk
    contradiction

/-- The predecessor of a gap coordinate is the preceding embedded gap
reaction, except at the first coordinate where it is the left fork. -/
theorem gap_cycle_predecessor
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (a : Fin l) (i : Fin (S.gapLength a + 1)) :
    next.symm ((S.gap a).idx i) =
      if h : 0 < i.val then
        (S.gap a).idx (finitePathPrev i h)
      else S.fork a := by
  split_ifs with hi
  · apply next.injective
    rw [next.apply_symm_apply]
    exact ((S.gap a).idx_prev_step i hi).symm
  · have hi0 : i = 0 := by
      apply Fin.ext
      exact Nat.eq_zero_of_not_pos hi
    subst i
    apply next.injective
    rw [next.apply_symm_apply]
    exact (S.wrap a).post.first_eq

/-- Reaction whose cycle edge enters a given gap coordinate. -/
def gapIncomingReaction
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (a : Fin l) (i : Fin (S.gapLength a + 1)) : Fin n :=
  if h : 0 < i.val then
    (S.gap a).idx (finitePathPrev i h)
  else S.fork a

@[simp] theorem gapIncomingReaction_zero
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (a : Fin l) : S.gapIncomingReaction a 0 = S.fork a := by
  simp [gapIncomingReaction]

@[simp] theorem gapIncomingReaction_succ
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (a : Fin l) (i : Fin (S.gapLength a)) :
    S.gapIncomingReaction a i.succ = (S.gap a).idx i.castSucc := by
  unfold gapIncomingReaction
  split_ifs with h
  · congr 1
  · simp at h

/-- Exactly one fork back branch enters a terminal gap coordinate, and no
back branch enters any earlier coordinate. -/
theorem gap_back_current_sum
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (J : Fin n → ℝ) (a : Fin l)
    (i : Fin (S.gapLength a + 1)) :
    (∑ k, match back k with
      | none => 0
      | some z => if (S.gap a).idx i = z then J k else 0) =
        if i = Fin.last (S.gapLength a) then J (S.fork (S.step a)) else 0 := by
  classical
  rw [S.sum_eq_fork_sum_add_gap_sum]
  have hgap :
      (∑ b, ∑ u, match back ((S.gap b).idx u) with
        | none => 0
        | some z => if (S.gap a).idx i = z then J ((S.gap b).idx u) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro u _
    rw [(S.gap b).nonfork u]
  rw [hgap, add_zero]
  by_cases hi : i = Fin.last (S.gapLength a)
  · subst i
    rw [Fintype.sum_eq_single (S.step a)]
    · rw [S.back_fork, S.step.symm_apply_apply]
      simp
    · intro b hb
      rw [S.back_fork]
      have hab : a ≠ S.step.symm b := by
        intro h
        apply hb
        rw [h, S.step.apply_symm_apply]
      have hne := S.gap_point_ne_other_gap hab
        (Fin.last (S.gapLength a))
        (Fin.last (S.gapLength (S.step.symm b)))
      simp [hne]
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro b _
    rw [S.back_fork]
    simp only
    rw [ite_eq_right]
    intro heq
    have hab : a = S.step.symm b := S.gap_owner a (S.step.symm b) i
      (Fin.last (S.gapLength (S.step.symm b))) heq
    subst a
    apply hi
    exact (S.gap (S.step.symm b)).idx.injective heq

/-- Global base stationarity specialized through the universal divergence
law.  This is one local transport equation valid at every gap coordinate;
endpoint behavior appears only through its two structural `if` terms. -/
theorem base_gap_current_balance
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e : Fin n → ℝ)
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (a : Fin l) (i : Fin (S.gapLength a + 1)) :
    (weight (S.gapIncomingReaction a i) : ℝ) *
        (p (S.gapIncomingReaction a i) - q (S.gapIncomingReaction a i)) -
        (p ((S.gap a).idx i) - q ((S.gap a).idx i)) +
      (if i = Fin.last (S.gapLength a) then
        p (S.fork (S.step a)) - q (S.fork (S.step a)) else 0) =
      e ((S.gap a).idx i) := by
  let J : Fin n → ℝ := fun k => p k - q k
  have hrow := hbase ((S.gap a).idx i)
  change (∑ k, sourceStoich next weight back ((S.gap a).idx i) k * J k) =
    e ((S.gap a).idx i) at hrow
  rw [sourceStoich_mul_current_eq_divergence next weight back J,
    S.gap_cycle_predecessor a i, S.gap_back_current_sum J a i] at hrow
  simpa [gapIncomingReaction, J] using hrow

/-- The base balance at a fork has exactly two current supports: its own
reaction and the terminal cycle reaction immediately preceding it.  Under
the source-minimal unit terminal weight this is the discrete divergence law
`J_terminal - J_fork = degradation_fork`.

This is the generating identity behind both the positive-current gauge and
the terminal equality used by the literal Schur estimates. -/
theorem base_fork_current_balance
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e : Fin n → ℝ)
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (j : Fin l)
    (hunit : weight ((S.gap (S.step.symm j)).idx
      (Fin.last (S.gapLength (S.step.symm j)))) = 1) :
    (p ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j)))) -
      q ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j))))) -
      (p (S.fork j) - q (S.fork j)) = e (S.fork j) := by
  classical
  let t := (S.gap (S.step.symm j)).idx
    (Fin.last (S.gapLength (S.step.symm j)))
  let f := S.fork j
  have htf : t ≠ f := by
    dsimp [t, f]
    exact S.gap_point_ne_fork j (S.step.symm j)
      (Fin.last (S.gapLength (S.step.symm j)))
  have htNext : next t = f := by
    dsimp [t, f]
    simpa using (S.wrap (S.step.symm j)).pre.terminal_next
  have hNt : sourceStoich next weight back f t = 1 := by
    rw [← htNext]
    rw [sourceStoich_successor_entry next weight back]
    · simpa [t] using hunit
    · simpa [htNext] using htf.symm
    · intro z hz
      have hnone := (S.gap (S.step.symm j)).nonfork
        (Fin.last (S.gapLength (S.step.symm j)))
      change back t = none at hnone
      rw [hnone] at hz
      contradiction
  have hfNext : f ≠ next f := by
    intro h
    apply (S.wrap j).post.fork_outside 0
    rw [(S.wrap j).post.first_eq]
    exact h
  have hNf : sourceStoich next weight back f f = -1 := by
    exact sourceStoich_source_entry next weight back hfNext
      (fun z hz => S.fork_ne_back_target j hz)
  have hoff : ∀ k, k ≠ t → k ≠ f →
      sourceStoich next weight back f k * (p k - q k) = 0 := by
    intro k hkt hkf
    have hnext : f ≠ next k := by
      intro h
      apply hkt
      apply next.injective
      simpa [htNext] using h.symm
    have hzero := sourceStoich_eq_zero_of_off_support next weight back
      hkf.symm hnext (fun z hz => S.fork_ne_back_target j hz)
    rw [hzero]
    ring
  have hrow := hbase f
  change (∑ k, sourceStoich next weight back f k * (p k - q k)) = e f at hrow
  rw [sum_eq_two_of_zero t f htf
    (fun k => sourceStoich next weight back f k * (p k - q k)) hoff] at hrow
  rw [hNt, hNf] at hrow
  dsimp [t, f] at hrow ⊢
  linarith

/-- The terminal flux identity in the exact form required by the Schur
transport lemmas. -/
theorem terminal_rate_eq_of_base_balance
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e : Fin n → ℝ)
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (j : Fin l)
    (hunit : weight ((S.gap (S.step.symm j)).idx
      (Fin.last (S.gapLength (S.step.symm j)))) = 1) :
    p ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j)))) =
      q ((S.gap (S.step.symm j)).idx
          (Fin.last (S.gapLength (S.step.symm j)))) +
        e (S.fork j) + (p (S.fork j) - q (S.fork j)) := by
  have h := S.base_fork_current_balance weight p q e hbase j hunit
  linarith

/-- Every fork base current is positive.  The proof adds the terminal and
right-fork divergence equations to cancel the return current, then invokes
one finite backward-transport theorem for the entire weighted stem. -/
theorem fork_current_pos_of_base_balance
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e : Fin n → ℝ)
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (hw : ∀ r, 0 < weight r) (he : ∀ r, 0 < e r)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (a : Fin l) :
    0 < p (S.fork a) - q (S.fork a) := by
  let s : Fin (S.gapLength a + 1) → ℝ := fun i =>
    (weight (S.gapIncomingReaction a i) : ℝ)
  let J : Fin (S.gapLength a + 1) → ℝ := fun i =>
    p (S.gapIncomingReaction a i) - q (S.gapIncomingReaction a i)
  let d : Fin (S.gapLength a + 1) → ℝ := fun i =>
    e ((S.gap a).idx i)
  have hs : ∀ i, 0 < s i := by
    intro i
    dsimp [s]
    exact_mod_cast hw (S.gapIncomingReaction a i)
  have hd : ∀ i, 0 < d i := by
    intro i
    exact he ((S.gap a).idx i)
  have hstep : ∀ i : Fin (S.gapLength a),
      s i.castSucc * J i.castSucc = J i.succ + d i.castSucc := by
    intro i
    have hrow := S.base_gap_current_balance weight p q e hbase a i.castSucc
    have hne : i.castSucc ≠ Fin.last (S.gapLength a) := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    rw [ite_eq_right hne] at hrow
    dsimp [s, J, d]
    rw [S.gapIncomingReaction_succ]
    linarith
  have hterminal : 0 < J (Fin.last (S.gapLength a)) := by
    have hgap := S.base_gap_current_balance weight p q e hbase a
      (Fin.last (S.gapLength a))
    have hstepSymm : S.step.symm (S.step a) = a :=
      S.step.symm_apply_apply a
    have hu : weight ((S.gap (S.step.symm (S.step a))).idx
        (Fin.last (S.gapLength (S.step.symm (S.step a))))) = 1 := by
      rw [hstepSymm]
      exact hunit a
    have hfork := S.base_fork_current_balance weight p q e hbase (S.step a) hu
    have hfork' :
        (p ((S.gap a).idx (Fin.last (S.gapLength a))) -
          q ((S.gap a).idx (Fin.last (S.gapLength a)))) -
            (p (S.fork (S.step a)) - q (S.fork (S.step a))) =
          e (S.fork (S.step a)) := by
      rw [hstepSymm] at hfork
      exact hfork
    have hprod : 0 < s (Fin.last (S.gapLength a)) *
        J (Fin.last (S.gapLength a)) := by
      have heSum : 0 < e ((S.gap a).idx (Fin.last (S.gapLength a))) +
          e (S.fork (S.step a)) := add_pos (he _) (he _)
      have heq : s (Fin.last (S.gapLength a)) *
          J (Fin.last (S.gapLength a)) =
        e ((S.gap a).idx (Fin.last (S.gapLength a))) +
          e (S.fork (S.step a)) := by
        simp only [ite_true] at hgap
        dsimp [s, J]
        linarith [hgap, hfork']
      rw [heq]
      exact heSum
    exact pos_of_mul_pos_right hprod (le_of_lt (hs _))
  have hleft := paper_fin_weighted_stem_current_pos
    (S.gapLength a) s J d hs hd hstep hterminal
  simpa [J] using hleft

end SourceCyclicNonemptyGapSystem

end TypeIIL

import proofs.TypeIIL.SourceBackFirstPreGap
import proofs.TypeIIL.SourceBaseCurrentTransport
import proofs.TypeIIL.SourceGlobalRowSplit

namespace TypeIIL

open scoped BigOperators

theorem sourceBackFirstCurrentMatrix_nonfork_eq_ordered
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n))
    {p q e rho : Fin n → ℝ} {r : Fin n}
    (hr : back r = none) (k : Fin n) :
    currentSecantKernelMatrixWith
        (sourceBackFirstSecantMatrix next weight back rho)
        (sourceStoich next weight back) p q e r k =
      currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e r k := by
  rw [currentSecantKernelMatrixWith_entry_expansion,
    currentSecantKernelMatrixWith_entry_expansion]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [sourceBackFirstSecantMatrix_nonfork next weight back rho hr,
    source_nonfork_ordered_entry next weight back hr]

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

noncomputable def backFirstCurrentMatrix
    (_S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  currentSecantKernelMatrixWith
    (sourceBackFirstSecantMatrix next weight back rho)
    (sourceStoich next weight back) p q e

noncomputable def backFirstGapDefect
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (a : Fin l) (i : Fin (S.gapLength a + 1)) : ℝ :=
  ∑ k, S.backFirstCurrentMatrix weight p q e rho ((S.gap a).idx i) k *
    (p k - q k)

noncomputable def backFirstForkDefect
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (a : Fin l) : ℝ :=
  ∑ k, S.backFirstCurrentMatrix weight p q e rho (S.fork a) k *
    (p k - q k)

/-- Every row has gain at least one in the back-first gauge.  Fork rows have
strict gain; gap rows reduce to the one-variable power secant. -/
theorem backFirstSecantMatrix_row_gain
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (rho : Fin n → ℝ)
    (hrho : ∀ r, 0 < rho r) (hw : ∀ r, 0 < weight r) (r : Fin n) :
    1 ≤ ∑ i, sourceBackFirstSecantMatrix next weight back rho r i := by
  rcases S.cover r with ⟨a, rfl⟩ | ⟨a, i, rfl⟩
  · apply le_of_lt
    apply sourceBackFirstSecantMatrix_row_gain_fork next weight back hrho
      (S.back_fork a)
    · simpa using (S.wrap a).post.back_ne_next
    · exact hw (S.fork a)
  · exact sourceBackFirstSecantMatrix_row_gain_nonfork next weight back hrho
      ((S.gap a).nonfork i) (hw ((S.gap a).idx i))

/-- The base current is a global weak supersolution of the back-first current
kernel.  This is the generating inequality behind all gap-defect signs. -/
theorem backFirstGapDefect_nonneg
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (hq : ∀ r, 0 ≤ q r) (he : ∀ r, 0 < e r)
    (hrho : ∀ r, 0 < rho r) (hw : ∀ r, 0 < weight r)
    (a : Fin l) (i : Fin (S.gapLength a + 1)) :
    0 ≤ S.backFirstGapDefect weight p q e rho a i := by
  unfold backFirstGapDefect backFirstCurrentMatrix
  exact currentSecantKernelMatrixWith_mul_baseCurrent_nonneg
    (sourceBackFirstSecantMatrix next weight back rho)
    (sourceStoich next weight back) (fun r => ne_of_gt (he r)) hbase hq
    (S.backFirstSecantMatrix_row_gain weight rho hrho hw)
    ((S.gap a).idx i)

/-- At each fork the same supersolution inequality is strict, because the
back target contributes one and the successor contributes a positive secant. -/
theorem backFirstForkDefect_pos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (hq : ∀ r, 0 < q r) (he : ∀ r, 0 < e r)
    (hrho : ∀ r, 0 < rho r) (hw : ∀ r, 0 < weight r)
    (a : Fin l) :
    0 < S.backFirstForkDefect weight p q e rho a := by
  unfold backFirstForkDefect backFirstCurrentMatrix
  rw [currentSecantKernelMatrixWith_mul_baseCurrent
    (sourceBackFirstSecantMatrix next weight back rho)
    (sourceStoich next weight back) (fun r => ne_of_gt (he r)) hbase]
  apply mul_pos (hq (S.fork a))
  apply sub_pos.mpr
  apply sourceBackFirstSecantMatrix_row_gain_fork next weight back hrho
    (S.back_fork a)
  · simpa using (S.wrap a).post.back_ne_next
  · exact hw (S.fork a)

/-- Back-first row ordering changes coefficients but not fork-row support:
only the preceding and following gap blocks can occur. -/
theorem backFirst_fork_row_other_gap_entry_zero
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (j a : Fin l) (i : Fin (S.gapLength a + 1))
    (haj : a ≠ j) (hapred : a ≠ S.step.symm j) :
    S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap a).idx i) = 0 := by
  let pred := S.step.symm j
  let z := (S.gap pred).idx (Fin.last (S.gapLength pred))
  have hr : back (S.fork j) = some z := by
    simpa [pred, z] using S.back_fork j
  have hz : z ≠ next (S.fork j) := by
    simpa [pred, z] using (S.wrap j).post.back_ne_next
  have hstep : S.step a ≠ j := by
    intro h
    apply hapred
    apply S.step.injective
    simpa [pred] using h
  have hstoFork :
      sourceStoich next weight back (S.fork j) ((S.gap a).idx i) = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact (S.gap_point_ne_fork j a i).symm
    · rcases S.next_gap_point_cases a i with ⟨u, hu⟩ | hu
      · rw [hu]
        exact (S.gap_point_ne_fork j a u).symm
      · rw [hu]
        exact S.fork.injective.ne hstep.symm
    · intro z' hz'
      rw [(S.gap a).nonfork i] at hz'
      contradiction
  have hstoNext :
      sourceStoich next weight back (next (S.fork j)) ((S.gap a).idx i) = 0 := by
    rw [← (S.wrap j).post.first_eq]
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact S.gap_point_ne_other_gap haj.symm 0 i
    · rcases S.next_gap_point_cases a i with ⟨u, hu⟩ | hu
      · rw [hu]
        exact S.gap_point_ne_other_gap haj.symm 0 u
      · rw [hu]
        exact S.gap_point_ne_fork (S.step a) j 0
    · intro z' hz'
      rw [(S.gap a).nonfork i] at hz'
      contradiction
  have hstoBack :
      sourceStoich next weight back z ((S.gap a).idx i) = 0 := by
    apply sourceStoich_eq_zero_of_off_support next weight back
    · exact S.gap_point_ne_other_gap hapred.symm
        (Fin.last (S.gapLength pred)) i
    · rcases S.next_gap_point_cases a i with ⟨u, hu⟩ | hu
      · rw [hu]
        exact S.gap_point_ne_other_gap hapred.symm
          (Fin.last (S.gapLength pred)) u
      · rw [hu]
        exact S.gap_point_ne_fork (S.step a) pred
          (Fin.last (S.gapLength pred))
    · intro z' hz'
      rw [(S.gap a).nonfork i] at hz'
      contradiction
  have hrk : S.fork j ≠ (S.gap a).idx i :=
    (S.gap_point_ne_fork j a i).symm
  unfold backFirstCurrentMatrix
  rw [sourceBackFirstCurrentMatrix_fork_entry next weight back hr hz]
  rw [ite_eq_right hrk, hstoFork, hstoNext, hstoBack]
  ring

noncomputable def backFirstGapLift
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (p q : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (a : Fin l) (i : Fin (S.gapLength a + 1)) : ℝ :=
  (p ((S.gap a).idx i) - q ((S.gap a).idx i)) +
    yw a i * (p (S.fork a) - q (S.fork a)) +
    xf a i * (p (S.fork (S.step a)) - q (S.fork (S.step a)))

noncomputable def backFirstGapCorrection
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j a : Fin l) : ℝ :=
  ∑ i, S.backFirstCurrentMatrix weight p q e rho
      (S.fork j) ((S.gap a).idx i) *
    S.backFirstGapLift p q xf yw a i

/-- Schur complement on fork coordinates, written using the two canonical
gap response columns. -/
noncomputable def backFirstReducedForkMatrix
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ) :
    Matrix (Fin l) (Fin l) ℝ := fun j b =>
  S.backFirstCurrentMatrix weight p q e rho (S.fork j) (S.fork b) -
    ∑ a, ∑ i,
      S.backFirstCurrentMatrix weight p q e rho
          (S.fork j) ((S.gap a).idx i) *
        ((if b = a then yw a i else 0) +
          if b = S.step a then xf a i else 0)

/-- The internal defect of the base current is exactly the gap block applied
to the lifted current. -/
theorem backFirstGapLift_solve_defect
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hgap : ∀ a, 0 < S.gapLength a)
    (a : Fin l) (i : Fin (S.gapLength a + 1)) :
    ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t *
        S.backFirstGapLift p q xf yw a t =
      S.backFirstGapDefect weight p q e rho a i := by
  let MO := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let MB := S.backFirstCurrentMatrix weight p q e rho
  let G := S.gap a
  let P := S.wrap a
  have hrowEq : ∀ k, MB (G.idx i) k = MO (G.idx i) k := by
    intro k
    exact sourceBackFirstCurrentMatrix_nonfork_eq_ordered next weight back
      (G.nonfork i) k
  have hsum := sum_eq_embedding_sum_add_two G.idx (S.fork a)
    (S.fork (S.step a))
    (fun k => MO (G.idx i) k * (p k - q k))
    (fun j => P.post.fork_outside j)
    (fun j => P.pre.fork_ne_idx j) P.left_ne_right
    (fun k hkl hkr hkg => by
      have hz := (S.globalColumnClosed a).entry_zero
        weight p q e rho i k hkl hkr hkg
      change MO (G.idx i) k = 0 at hz
      change MO (G.idx i) k * (p k - q k) = 0
      rw [hz]
      ring)
  have hleft := P.internal_left_column_eq_forcing weight p q e rho i
  have hright := P.internal_right_column_eq_forcing
    (hgap a) weight p q e rho (hunit a) i
  change MO (G.idx i) (S.fork a) =
      sourceWrapLeftForcing (G.gapA p e) (weight (S.fork a)) i at hleft
  change MO (G.idx i) (S.fork (S.step a)) =
      sourceWrapForwardForcing (G.gapA p e) (G.gapC weight q e rho) i at hright
  have hD : ∀ t,
      (S.gap a).restrictedCurrentMatrix weight p q e rho i t =
        MO (G.idx i) (G.idx t) := by
    intro t
    rfl
  have hywMO :
      ∑ t, MO (G.idx i) (G.idx t) * yw a t =
        sourceWrapLeftForcing (G.gapA p e) (weight (S.fork a)) i := by
    rw [← hyw a i]
    apply Finset.sum_congr rfl
    intro t _
    rw [hD t]
  have hxfMO :
      ∑ t, MO (G.idx i) (G.idx t) * xf a t =
        sourceWrapForwardForcing (G.gapA p e)
          (G.gapC weight q e rho) i := by
    rw [← hxf a i]
    apply Finset.sum_congr rfl
    intro t _
    rw [hD t]
  unfold backFirstGapLift backFirstGapDefect
  simp_rw [hD]
  change _ = ∑ k, MB (G.idx i) k * (p k - q k)
  rw [show (∑ k, MB (G.idx i) k * (p k - q k)) =
      ∑ k, MO (G.idx i) k * (p k - q k) by
    apply Finset.sum_congr rfl
    intro k _
    rw [hrowEq k]]
  rw [hsum]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hywMO, hxfMO,
    hleft, hright]

/-- Every eliminated gap contributes a nonpositive correction to every fork
row.  The proof is local only in topology: the following gap uses positivity
of the Green operator, the preceding gap uses terminal current transport, and
all other gaps vanish by support. -/
theorem backFirstGapCorrection_nonpos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i)
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hgap : ∀ a, 0 < S.gapLength a)
    (j a : Fin l) :
    S.backFirstGapCorrection weight p q e rho xf yw j a ≤ 0 := by
  by_cases haj : a = j
  · subst a
    unfold backFirstGapCorrection backFirstCurrentMatrix
    apply (S.wrap j).post.backFirst_fork_postGap_green_correction_nonpos
      weight p q e rho hp (fun r => le_of_lt (hq r)) he hrho hw
      (S.backFirstGapLift p q xf yw j)
      (S.backFirstGapDefect weight p q e rho j)
    · exact S.backFirstGapDefect_nonneg weight p q e rho hbase
        (fun r => le_of_lt (hq r)) he hrho hw j
    · exact S.backFirstGapLift_solve_defect weight p q e rho xf yw
        hxf hyw hunit hgap j
  · by_cases hapred : a = S.step.symm j
    · subst a
      let pred := S.step.symm j
      have hJFork : 0 < p (S.fork j) - q (S.fork j) :=
        S.fork_current_pos_of_base_balance weight p q e hbase hw he hunit j
      have hpLast := S.terminal_rate_eq_of_base_balance
        weight p q e hbase j (hunit pred)
      have hcorr := (S.wrap pred).pre.backFirst_fork_preGap_correction_nonpos
        (hgap pred) weight p q e rho
        (p (S.fork j) - q (S.fork j)) (hunit pred)
        (by rw [S.step.apply_symm_apply]; ring)
        (by simpa [pred] using hpLast) hp (fun r => le_of_lt (hq r))
        (hq _) (hq _) he hrho hw hJFork
        (S.backFirstGapLift p q xf yw pred)
        (S.backFirstGapDefect weight p q e rho pred)
        (S.backFirstGapDefect_nonneg weight p q e rho hbase
          (fun r => le_of_lt (hq r)) he hrho hw pred)
        (S.backFirstGapLift_solve_defect weight p q e rho xf yw
          hxf hyw hunit hgap pred)
      simpa [backFirstGapCorrection, backFirstCurrentMatrix, pred] using hcorr
    · unfold backFirstGapCorrection
      apply Finset.sum_nonpos
      intro i _
      rw [S.backFirst_fork_row_other_gap_entry_zero weight p q e rho
        j a i haj hapred]
      simp

/-- The reduced fork operator applied to the positive fork-current vector is
the strict fork defect minus the sum of all (nonpositive) eliminated-gap
corrections.  This is the global residual identity; no row is exceptional. -/
theorem backFirstReducedForkMatrix_mul_baseCurrent
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) :
    ∑ b, S.backFirstReducedForkMatrix weight p q e rho xf yw j b *
        (p (S.fork b) - q (S.fork b)) =
      S.backFirstForkDefect weight p q e rho j -
        ∑ a, S.backFirstGapCorrection weight p q e rho xf yw j a := by
  let M := S.backFirstCurrentMatrix weight p q e rho
  let J : Fin n → ℝ := fun k => p k - q k
  have hpoint : ∀ a i,
      ∑ b,
          (M (S.fork j) ((S.gap a).idx i) *
              ((if b = a then yw a i else 0) +
                if b = S.step a then xf a i else 0)) *
            J (S.fork b) =
        M (S.fork j) ((S.gap a).idx i) *
          (yw a i * J (S.fork a) +
            xf a i * J (S.fork (S.step a))) := by
    intro a i
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have htriple :
      ∑ b, (∑ a, ∑ i,
          M (S.fork j) ((S.gap a).idx i) *
            ((if b = a then yw a i else 0) +
              if b = S.step a then xf a i else 0)) * J (S.fork b) =
        ∑ a, ∑ i, M (S.fork j) ((S.gap a).idx i) *
          (yw a i * J (S.fork a) +
            xf a i * J (S.fork (S.step a))) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact hpoint a i
  have hpartition := S.sum_eq_fork_sum_add_gap_sum
    (fun k => M (S.fork j) k * J k)
  have hforkDefect :
      S.backFirstForkDefect weight p q e rho j =
        ∑ k, M (S.fork j) k * J k := by
    rfl
  have hcorrection :
      (∑ a, S.backFirstGapCorrection weight p q e rho xf yw j a) =
        ∑ a, ∑ i, M (S.fork j) ((S.gap a).idx i) *
          (J ((S.gap a).idx i) + yw a i * J (S.fork a) +
            xf a i * J (S.fork (S.step a))) := by
    rfl
  have hsplit :
      (∑ a, ∑ i, M (S.fork j) ((S.gap a).idx i) *
          (J ((S.gap a).idx i) + yw a i * J (S.fork a) +
            xf a i * J (S.fork (S.step a)))) =
        (∑ a, ∑ i, M (S.fork j) ((S.gap a).idx i) *
          J ((S.gap a).idx i)) +
        ∑ a, ∑ i, M (S.fork j) ((S.gap a).idx i) *
          (yw a i * J (S.fork a) +
            xf a i * J (S.fork (S.step a))) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    ring
  unfold backFirstReducedForkMatrix
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  change (∑ b, M (S.fork j) (S.fork b) * J (S.fork b)) - _ = _
  rw [htriple]
  rw [hforkDefect, hcorrection, hpartition, hsplit]
  ring

/-- The base fork-current vector is a strict global supersolution for the
reduced fork operator.  One argument closes all rows simultaneously. -/
theorem backFirstReducedForkMatrix_mul_baseCurrent_pos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i)
    (hbase : TypeII3.BaseFluxBalance
      (sourceStoich next weight back) p q e)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : ∀ a,
      weight ((S.gap a).idx (Fin.last (S.gapLength a))) = 1)
    (hgap : ∀ a, 0 < S.gapLength a)
    (j : Fin l) :
    0 < ∑ b, S.backFirstReducedForkMatrix weight p q e rho xf yw j b *
      (p (S.fork b) - q (S.fork b)) := by
  rw [S.backFirstReducedForkMatrix_mul_baseCurrent weight p q e rho xf yw j]
  have hfork := S.backFirstForkDefect_pos weight p q e rho hbase hq he
    hrho hw j
  have hcorrection :
      ∑ a, S.backFirstGapCorrection weight p q e rho xf yw j a ≤ 0 := by
    apply Finset.sum_nonpos
    intro a _
    exact S.backFirstGapCorrection_nonpos weight p q e rho xf yw hxf hyw
      hbase hp hq he hrho hw hunit hgap j a
  linarith

end SourceCyclicNonemptyGapSystem

end TypeIIL

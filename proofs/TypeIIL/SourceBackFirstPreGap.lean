module

public import proofs.TypeIIL.SourceBackFirstSecant
public import proofs.TypeIIL.SourceForkGapAdapter

@[expose] public section

namespace TypeIIL

open scoped BigOperators

/-- Entry expansion of a back-first fork row.  The coefficient-one back
factor and the positive weighted-successor factor are the only secant ports. -/
theorem sourceBackFirstCurrentMatrix_fork_entry
    {n : ℕ} (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n))
    {p q e rho : Fin n → ℝ} {r z : Fin n}
    (hr : back r = some z) (hz : z ≠ next r) (k : Fin n) :
    currentSecantKernelMatrixWith
        (sourceBackFirstSecantMatrix next weight back rho)
        (sourceStoich next weight back) p q e r k =
      (if r = k then 1 else 0) -
          (p r / e r) * sourceStoich next weight back r k +
        q r * ((1 / e z) * sourceStoich next weight back z k +
          ((rho z * TypeII3.secantPoly (rho (next r)) 1 (weight r)) /
              e (next r)) *
            sourceStoich next weight back (next r) k) := by
  rw [currentSecantKernelMatrixWith_entry_expansion]
  congr 1
  have hpoint : ∀ i,
      (sourceBackFirstSecantMatrix next weight back rho r i / e i) *
          sourceStoich next weight back i k =
        (if i = z then (1 / e z) * sourceStoich next weight back z k else 0) +
        (if i = next r then
          ((rho z * TypeII3.secantPoly (rho (next r)) 1 (weight r)) /
              e (next r)) *
            sourceStoich next weight back (next r) k else 0) := by
    intro i
    rw [sourceBackFirstSecantMatrix_fork next weight back rho hr]
    by_cases hiz : i = z
    · subst i
      simp [hz]
    · by_cases hin : i = next r
      · subst i
        simp [Ne.symm hz]
      · simp [hiz, hin]
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp

namespace SourcePreForkGap

variable {n m : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}
  {G : SourceGapEmbedding next back m} {fork : Fin n}

/-- The preceding-gap boundary functional in the back-first gauge.  It is
uniform: no comparison between ambient coordinate labels occurs. -/
theorem backFirst_fork_preGap_entry
    (P : SourcePreForkGap G fork) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (j : Fin (m + 1)) :
    currentSecantKernelMatrixWith
        (sourceBackFirstSecantMatrix next weight back rho)
        (sourceStoich next weight back) p q e fork (G.idx j) =
      if j = finitePathPrev (Fin.last m) (by simpa using hm) then
        (q fork / e (G.idx (Fin.last m))) * weight (G.idx j)
      else if j = Fin.last m then
        -(p fork / e fork + q fork / e (G.idx (Fin.last m)))
      else 0 := by
  let last : Fin (m + 1) := Fin.last m
  let prev : Fin (m + 1) := finitePathPrev last (by simpa [last] using hm)
  let z : Fin n := G.idx last
  have hznext : z ≠ next fork := by
    simpa [z, last] using P.terminal_ne_fork_successor
  have hzf : z ≠ fork := by simpa [z, last] using P.terminal_ne_fork
  have hforkz : back fork = some z := by simpa [z, last] using P.fork_back
  rw [sourceBackFirstCurrentMatrix_fork_entry next weight back hforkz hznext]
  by_cases hjlast : j = last
  · subst j
    have hprevlast : last ≠ prev := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [last, prev, finitePathPrev] at hv
      omega
    have hNfork : sourceStoich next weight back fork z = weight z := by
      have h := sourceStoich_successor_entry next weight back
        (k := z) (by simpa [z, last, P.terminal_next] using
          (G.idx_ne_next last).symm) (by
            intro x hx
            have hn := G.nonfork last
            rw [hn] at hx
            contradiction)
      simpa [z, last, P.terminal_next] using h
    have hNnext : sourceStoich next weight back (next fork) z = 0 := by
      apply sourceStoich_eq_zero_of_off_support next weight back
      · exact P.fork_successor_outside last
      · intro h
        apply P.fork_ne_next
        calc
          fork = next z := P.terminal_next.symm
          _ = next fork := h.symm
      · intro x hx
        have hn := G.nonfork last
        rw [hn] at hx
        contradiction
    have hNz : sourceStoich next weight back z z = -1 :=
      sourceStoich_source_entry next weight back (G.idx_ne_next last) (by
        intro x hx
        have hn := G.nonfork last
        rw [hn] at hx
        contradiction)
    rw [ite_eq_right (P.fork_ne_idx last), hNfork, hNz, hNnext]
    rw [ite_eq_right hprevlast, ite_eq_left rfl]
    rw [show weight z = 1 by simpa [z, last] using hunit]
    ring
  · by_cases hjprev : j = prev
    · subst j
      have hstep : next (G.idx prev) = z := by
        simpa [z, last, prev] using
          G.idx_prev_step last (by simpa [last] using hm)
      have hNfork : sourceStoich next weight back fork (G.idx prev) = 0 := by
        apply sourceStoich_eq_zero_of_off_support next weight back
        · exact P.fork_ne_idx prev
        · simpa [hstep] using hzf.symm
        · intro x hx
          have hn := G.nonfork prev
          rw [hn] at hx
          contradiction
      have hNnext :
          sourceStoich next weight back (next fork) (G.idx prev) = 0 := by
        apply sourceStoich_eq_zero_of_off_support next weight back
        · exact P.fork_successor_outside prev
        · simpa [hstep] using hznext.symm
        · intro x hx
          have hn := G.nonfork prev
          rw [hn] at hx
          contradiction
      have hNz : sourceStoich next weight back z (G.idx prev) =
          weight (G.idx prev) := by
        have hnextne : next (G.idx prev) ≠ G.idx prev := by
          rw [hstep]
          exact (G.idx_prev_ne last (by simpa [last] using hm)).symm
        have hs := sourceStoich_successor_entry next weight back hnextne (by
          intro x hx
          have hn := G.nonfork prev
          rw [hn] at hx
          contradiction)
        simpa [hstep] using hs
      rw [ite_eq_right (P.fork_ne_idx prev), hNfork, hNz, hNnext]
      rw [ite_eq_left rfl]
      ring
    · have hjz : G.idx j ≠ z := by
        intro h
        apply hjlast
        exact G.idx.injective (by simpa [z, last] using h)
      have hnextj_ne_fork : next (G.idx j) ≠ fork := by
        intro h
        have hsame : next (G.idx j) = next z := h.trans P.terminal_next.symm
        exact hjz (next.injective hsame)
      have hnextj_ne_z : next (G.idx j) ≠ z := by
        intro h
        rcases (G.predecessor_support last j).mp (by simpa [z, last] using h)
          with ⟨_, hj⟩
        apply hjprev
        simpa [prev, last] using hj
      have hNfork : sourceStoich next weight back fork (G.idx j) = 0 := by
        apply sourceStoich_eq_zero_of_off_support next weight back
        · exact P.fork_ne_idx j
        · exact hnextj_ne_fork.symm
        · intro x hx
          have hn := G.nonfork j
          rw [hn] at hx
          contradiction
      have hNnext : sourceStoich next weight back (next fork) (G.idx j) = 0 := by
        apply sourceStoich_eq_zero_of_off_support next weight back
        · exact P.fork_successor_outside j
        · intro h
          apply P.fork_ne_idx j
          exact next.injective h
        · intro x hx
          have hn := G.nonfork j
          rw [hn] at hx
          contradiction
      have hNz : sourceStoich next weight back z (G.idx j) = 0 := by
        apply sourceStoich_eq_zero_of_off_support next weight back
        · exact hjz.symm
        · exact hnextj_ne_z.symm
        · intro x hx
          have hn := G.nonfork j
          rw [hn] at hx
          contradiction
      rw [ite_eq_right (P.fork_ne_idx j), hNfork, hNz, hNnext]
      simp [last, prev, hjlast, hjprev]

theorem backFirst_fork_preGap_mul
    (P : SourcePreForkGap G fork) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (y : Fin (m + 1) → ℝ) :
    ∑ j, currentSecantKernelMatrixWith
          (sourceBackFirstSecantMatrix next weight back rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * y j =
      (q fork / e (G.idx (Fin.last m))) *
          weight (G.idx (finitePathPrev (Fin.last m) (by simpa using hm))) *
            y (finitePathPrev (Fin.last m) (by simpa using hm)) -
        (p fork / e fork + q fork / e (G.idx (Fin.last m))) *
          y (Fin.last m) := by
  simp_rw [P.backFirst_fork_preGap_entry hm weight p q e rho hunit]
  have hne : finitePathPrev (Fin.last m) (by simpa using hm) ≠ Fin.last m := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [finitePathPrev] at hv
    omega
  let prev : Fin (m + 1) := finitePathPrev (Fin.last m) (by simpa using hm)
  let last : Fin (m + 1) := Fin.last m
  let A : Fin (m + 1) → ℝ := fun x =>
    (q fork / e (G.idx (Fin.last m))) * weight (G.idx x) * y x
  let B : Fin (m + 1) → ℝ := fun x =>
    -(p fork / e fork + q fork / e (G.idx (Fin.last m))) * y x
  simp_rw [ite_mul, zero_mul]
  have hlp : last ≠ prev := by simpa [prev, last] using hne.symm
  have hsplit : ∀ x : Fin (m + 1),
      (if x = prev then A x else if x = last then B x else 0) =
        (if x = prev then A x else 0) + (if x = last then B x else 0) := by
    intro x
    by_cases hx : x = prev
    · subst x
      have hpl : prev ≠ last := by simpa [prev, last] using hne
      simp [hpl]
    · by_cases hxl : x = last <;> simp [hx, hxl, hlp]
  change (∑ x, if x = prev then A x else if x = last then B x else 0) = _
  calc
    _ = ∑ x, ((if x = prev then A x else 0) +
          (if x = last then B x else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact hsplit x
    _ = (∑ x, if x = prev then A x else 0) +
          ∑ x, if x = last then B x else 0 := Finset.sum_add_distrib
    _ = A prev + B last := by simp
    _ = _ := by dsimp [A, B, prev, last]; ring

/-- Uniform arbitrary-length preceding correction theorem.  This is the old
nonwrap result with the coordinate-order premise removed by the back-first
secant gauge. -/
theorem backFirst_fork_preGap_correction_nonpos
    (P : SourcePreForkGap G fork) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) (JFork : ℝ)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (hpFork : p fork = q fork + JFork)
    (hpLast : p (G.idx (Fin.last m)) =
      q (G.idx (Fin.last m)) + e fork + JFork)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 ≤ q r)
    (hqLast : 0 < q (G.idx (Fin.last m))) (hqFork : 0 < q fork)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hJFork : 0 < JFork)
    (y b : Fin (m + 1) → ℝ)
    (hb : ∀ i, 0 ≤ b i)
    (hsolve : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * y j = b i) :
    ∑ j, currentSecantKernelMatrixWith
          (sourceBackFirstSecantMatrix next weight back rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * y j ≤ 0 := by
  rw [P.backFirst_fork_preGap_mul hm weight p q e rho hunit y]
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hsolve
  let last : Fin (m + 1) := Fin.last m
  let prev : Fin (m + 1) := finitePathPrev last (by simpa [last] using hm)
  let h := q fork / e (G.idx last)
  let g := p fork / e fork
  have hh : 0 ≤ h := div_nonneg (le_of_lt hqFork) (le_of_lt (he _))
  have ht : 0 ≤ G.gapS weight prev := le_of_lt (G.gapS_pos hw prev)
  have hAlast : 0 < G.gapA p e last := div_pos (hp _) (he _)
  have hsource := source_terminal_transport
    (eBack := e (G.idx last)) (eFork := e fork)
    (qLast := q (G.idx last)) (qFork := q fork) (JFork := JFork)
    (s := G.gapS weight prev) (he _) (he _) hqLast hqFork hJFork ht
  have htransport :
      h * G.gapS weight prev *
          (1 + G.gapA p e last +
            G.gapC weight q e rho last * G.gapS weight last) ≤
        (g + h) * (G.gapA p e last * G.gapS weight prev) := by
    dsimp only [h, g]
    rw [hpFork]
    unfold SourceGapEmbedding.gapA SourceGapEmbedding.gapC
      SourceGapEmbedding.gapS
    have hterminal : next (G.idx last) = fork := by
      simpa [last] using P.terminal_next
    have hunitLast : weight (G.idx last) = 1 := by
      simpa [last] using hunit
    have hpLastLocal : p (G.idx last) = q (G.idx last) + e fork + JFork := by
      simpa [last] using hpLast
    rw [hterminal, hunitLast, hpLastLocal]
    simp [TypeII3.secantPoly] at hsource ⊢
    unfold SourceGapEmbedding.gapS at hsource
    convert hsource using 1
    all_goals ring_nf
  have hgreen := finiteSourcePath_terminal_mixed_boundary_nonpos hm
    (G.gapA_nonneg (fun r => le_of_lt (hp r)) he)
    (G.gapC_nonneg hq he hrho hw) (G.gapS_pos hw) hAlast hb hsolve
    hh ht (by simpa [last, prev, h, g] using htransport)
  simpa [last, prev, h, g, SourceGapEmbedding.gapS] using hgreen

end SourcePreForkGap

namespace SourcePostForkGap

variable {n m : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}
  {G : SourceGapEmbedding next back m} {fork z : Fin n}

theorem backFirst_fork_postGap_entry
    (P : SourcePostForkGap G fork z)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (j : Fin (m + 1)) :
    currentSecantKernelMatrixWith
        (sourceBackFirstSecantMatrix next weight back rho)
        (sourceStoich next weight back) p q e fork (G.idx j) =
      if j = 0 then
        -(q fork * ((rho z * TypeII3.secantPoly (rho (next fork)) 1
            (weight fork)) / e (next fork)))
      else 0 := by
  rw [sourceBackFirstCurrentMatrix_fork_entry next weight back P.fork_back
    P.back_ne_next]
  have hNfork : sourceStoich next weight back fork (G.idx j) = 0 :=
    sourceStoich_eq_zero_of_off_support next weight back
      (P.fork_outside j) (P.fork_not_successor j)
      (by intro x hx; simp [G.nonfork j] at hx)
  have hNz : sourceStoich next weight back z (G.idx j) = 0 :=
    sourceStoich_eq_zero_of_off_support next weight back
      (P.back_outside j) (P.back_not_successor j)
      (by intro x hx; simp [G.nonfork j] at hx)
  have hNnext : sourceStoich next weight back (next fork) (G.idx j) =
      if j = 0 then -1 else 0 := by
    by_cases hj : j = 0
    · subst j
      rw [← P.first_eq]
      rw [sourceStoich_source_entry next weight back (G.idx_ne_next 0)
        (by intro x hx; simp [G.nonfork 0] at hx)]
      simp
    · rw [ite_eq_right hj]
      apply sourceStoich_eq_zero_of_off_support next weight back
      · intro h
        apply hj
        exact G.idx.injective (by simpa [P.first_eq] using h.symm)
      · intro h
        have hs : next (G.idx j) = G.idx 0 := by
          simpa [P.first_eq] using h.symm
        rcases (G.predecessor_support 0 j).mp hs with ⟨hzero, _⟩
        simp at hzero
      · intro x hx
        simp [G.nonfork j] at hx
  rw [ite_eq_right (P.fork_outside j), hNfork, hNz, hNnext]
  by_cases hj : j = 0 <;> simp [hj]

theorem backFirst_fork_postGap_mul
    (P : SourcePostForkGap G fork z)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (y : Fin (m + 1) → ℝ) :
    ∑ j, currentSecantKernelMatrixWith
          (sourceBackFirstSecantMatrix next weight back rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * y j =
      -(q fork * ((rho z * TypeII3.secantPoly (rho (next fork)) 1
          (weight fork)) / e (next fork))) * y 0 := by
  simp_rw [P.backFirst_fork_postGap_entry weight p q e rho]
  simp

theorem backFirst_fork_postGap_green_correction_nonpos
    (P : SourcePostForkGap G fork z)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (y b : Fin (m + 1) → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hsolve : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * y j = b i) :
    ∑ j, currentSecantKernelMatrixWith
          (sourceBackFirstSecantMatrix next weight back rho)
          (sourceStoich next weight back) p q e fork (G.idx j) * y j ≤ 0 := by
  rw [P.backFirst_fork_postGap_mul weight p q e rho y]
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hsolve
  have hy := zmatrix_solution_nonneg
    (finiteSourcePathMatrix (G.gapA p e) (G.gapC weight q e rho)
      (G.gapS weight))
    (finiteSourcePathWeight (G.gapS weight)) y b
    (finiteSourcePathMatrix_offdiag_nonpos
      (G.gapA_nonneg (fun r => le_of_lt (hp r)) he)
      (G.gapC_nonneg hq he hrho hw)
      (fun i => le_of_lt (G.gapS_pos hw i)))
    (finiteSourcePathWeight_pos (G.gapS_pos hw))
    (finiteSourcePathMatrix_mul_weight_pos
      (G.gapA_nonneg (fun r => le_of_lt (hp r)) he)
      (G.gapC_nonneg hq he hrho hw) (G.gapS_pos hw)) hb hsolve
  have hcoeff : 0 ≤ q fork *
      ((rho z * TypeII3.secantPoly (rho (next fork)) 1 (weight fork)) /
        e (next fork)) := by
    exact mul_nonneg (hq fork) (div_nonneg
      (mul_nonneg (le_of_lt (hrho z))
        (TypeII3.secantPoly_nonneg (hrho _) (by norm_num) _))
      (le_of_lt (he _)))
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoeff) (hy 0)

end SourcePostForkGap

end TypeIIL

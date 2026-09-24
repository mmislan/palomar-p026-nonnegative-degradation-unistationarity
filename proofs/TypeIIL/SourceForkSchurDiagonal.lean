import proofs.TypeIIL.SourceWrapFollowingBudget
import proofs.TypeIIL.SourceForkSchurResponse

namespace TypeIIL

open scoped BigOperators

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

/-- Exact bookkeeping for the right diagonal of one literal positive gap.
The preceding gap supplies the condensed right core; the following gap
supplies precisely `k * (scale + yw 0 - xf 0)`. -/
theorem forkSchurSelf_sub_next_eq_right_core_add_following
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hnext : 0 < S.gapLength (S.step j))
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1) :
    let r := S.step j
    let last := Fin.last (S.gapLength j)
    let prev := finitePathPrev last (by exact hm)
    let g := p (S.fork r) / e (S.fork r)
    let h := q (S.fork r) *
      (sourceForkBackCoeff next weight back rho (S.fork r)
        ((S.gap j).idx last) / e ((S.gap j).idx last))
    let k := q (S.fork r) *
      (sourceForkNextCoeff next weight back rho (S.fork r) /
        e (next (S.fork r)))
    S.forkSchurSelfCoefficient weight p q e rho xf yw r -
        S.forkSchurNextCoefficient weight p q e rho xf r =
      (1 + g + h -
        (h * weight ((S.gap j).idx prev) * xf j prev -
          (g + h) * xf j last)) +
        k * ((weight (S.fork r) : ℝ) + yw r 0 - xf r 0) := by
  let r := S.step j
  let last : Fin (S.gapLength j + 1) := Fin.last (S.gapLength j)
  let prev := finitePathPrev last (by exact hm)
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let g := p (S.fork r) / e (S.fork r)
  let h := q (S.fork r) *
    (sourceForkBackCoeff next weight back rho (S.fork r)
      ((S.gap j).idx last) / e ((S.gap j).idx last))
  let k := q (S.fork r) *
    (sourceForkNextCoeff next weight back rho (S.fork r) /
      e (next (S.fork r)))
  have hdiag := sourceOrderedCurrentMatrix_fork_diagonal
    next weight back (p := p) (q := q) (e := e) (rho := rho)
    (r := S.fork r) (z := (S.gap j).idx last)
    (by simpa [r, last] using (S.wrap j).pre.fork_back)
    (by simpa [r, last] using (S.wrap j).pre.terminal_ne_fork_successor)
    (by simpa [r] using (S.wrap j).pre.fork_ne_next)
    (by simpa [r, last] using (S.wrap j).pre.terminal_ne_fork)
  have hpre := (S.wrap j).pre.fork_preGap_mul hm
    weight p q e rho hunit (xf j)
  have hpostY := (S.wrap r).post.fork_postGap_mul
    weight p q e rho (yw r)
  have hpostX := (S.wrap r).post.fork_postGap_mul
    weight p q e rho (xf r)
  have hdirect := (S.wrap r).left_right_entry_zero hnext
    weight p q e rho
  change M (S.fork r) (S.fork r) = _ at hdiag
  change (∑ i, M (S.fork r) ((S.gap j).idx i) * xf j i) = _ at hpre
  change (∑ i, M (S.fork r) ((S.gap r).idx i) * yw r i) = _ at hpostY
  change (∑ i, M (S.fork r) ((S.gap r).idx i) * xf r i) = _ at hpostX
  change M (S.fork r) (S.fork (S.step r)) = 0 at hdirect
  simp only [forkSchurSelfCoefficient, forkSchurNextCoefficient]
  change
    (M (S.fork r) (S.fork r) -
        (∑ i, M (S.fork r)
          ((S.gap (S.step.symm r)).idx i) * xf (S.step.symm r) i) -
        ∑ i, M (S.fork r) ((S.gap r).idx i) * yw r i) -
      (M (S.fork r) (S.fork (S.step r)) -
        ∑ i, M (S.fork r) ((S.gap r).idx i) * xf r i) = _
  rw [show S.step.symm r = j by simp [r], hdiag, hpre, hpostY,
    hpostX, hdirect]
  dsimp [g, h, k, prev, last]
  ring

/-- Consequently the genuine literal coefficient `B-F` is bounded below by
the condensed right core.  Both adjacent gap responses are the actual Schur
columns; no independent sign assumption is made on either mixed response. -/
theorem right_core_le_forkSchurSelf_sub_next
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 1 < S.gapLength j)
    (hnext : 0 < S.gapLength (S.step j))
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hnextUnit : weight ((S.gap (S.step j)).idx
      (Fin.last (S.gapLength (S.step j)))) = 1)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i) :
    let r := S.step j
    let kLeft := q (S.fork j) *
      (sourceForkNextCoeff next weight back rho (S.fork j) /
        e (next (S.fork j)))
    let g := p (S.fork r) / e (S.fork r)
    let h := q (S.fork r) *
      (sourceForkBackCoeff next weight back rho (S.fork r)
        ((S.gap j).idx (Fin.last (S.gapLength j))) /
          e ((S.gap j).idx (Fin.last (S.gapLength j))))
    let eff := (S.gap j).properWrapState weight p q e rho
      (weight (S.fork j)) kLeft
    let Aeff := wrapCondensedA eff.A
      (finitePathNatLift ((S.gap j).gapA p e) (S.gapLength j))
      (finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1))
    let heff := wrapCondensedH eff.A
      (finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) h
    let d := 1 + Aeff +
      finitePathNatLift ((S.gap j).gapC weight q e rho) (S.gapLength j)
    (d + g + heff) / d ≤
      S.forkSchurSelfCoefficient weight p q e rho xf yw r -
        S.forkSchurNextCoefficient weight p q e rho xf r := by
  let r := S.step j
  let m := S.gapLength j
  let mr := S.gapLength r
  let kLeft := q (S.fork j) *
    (sourceForkNextCoeff next weight back rho (S.fork j) /
      e (next (S.fork j)))
  let g := p (S.fork r) / e (S.fork r)
  let h := q (S.fork r) *
    (sourceForkBackCoeff next weight back rho (S.fork r)
      ((S.gap j).idx (Fin.last m)) / e ((S.gap j).idx (Fin.last m)))
  let k := q (S.fork r) *
    (sourceForkNextCoeff next weight back rho (S.fork r) /
      e (next (S.fork r)))
  have hm0 : 0 < m := by omega
  have hscaleLeft : 0 < (weight (S.fork j) : ℝ) := by
    exact_mod_cast hw (S.fork j)
  have hkLeft : 0 < kLeft := mul_pos (hq _)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw _) (he _))
  have hfirst :
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho 0 t * xf j t =
        0 := by
    have hx := hxf j 0
    have h0pen : (0 : ℕ) ≠ m - 1 := by omega
    have h0last : (0 : ℕ) ≠ m := by omega
    simpa [sourceWrapForwardForcing, m, h0pen, h0last] using hx
  have hrows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m - 1 →
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t * xf j t =
        0 := by
    intro i hi him
    have hipen : i.val ≠ m - 1 := by omega
    have hilast : i.val ≠ m := by omega
    simpa [sourceWrapForwardForcing, m, hipen, hilast] using hxf j i
  have hpen :
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho
          ⟨m - 1, by omega⟩ t * xf j t =
        (S.gap j).gapC weight q e rho ⟨m - 1, by omega⟩ := by
    have hx := hxf j ⟨m - 1, by omega⟩
    simpa [sourceWrapForwardForcing, m] using hx
  have hterminal :
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho
          (Fin.last m) t * xf j t =
        -((S.gap j).gapA p e (Fin.last m) +
          (S.gap j).gapC weight q e rho (Fin.last m)) := by
    have hx := hxf j (Fin.last m)
    have hne : m ≠ m - 1 := by omega
    simpa [sourceWrapForwardForcing, m, hne] using hx
  have hcore := (S.gap j).restricted_right_diagonal_core_eq hm
    weight p q e rho (xf j) hp hq he hrho hw hscaleLeft hkLeft
    (by simpa [SourceGapEmbedding.gapS] using hunit)
    hfirst hrows hpen hterminal (h := h) (g := g)
  have hprevEq :
      (⟨m - 1, by omega⟩ : Fin (m + 1)) =
        finitePathPrev (Fin.last m) hm0 := by
    apply Fin.ext
    simp [finitePathPrev]
  have hlastEq : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := by
    apply Fin.ext
    simp
  have hsLift :
      finitePathNatLift ((S.gap j).gapS weight) (m - 1) =
        (weight ((S.gap j).idx
          (finitePathPrev (Fin.last m) hm0)) : ℝ) := by
    rw [finitePathNatLift_of_lt (i := m - 1)
      ((S.gap j).gapS weight) (by omega), hprevEq]
    rfl
  have hxPrevLift : finitePathNatLift (xf j) (m - 1) =
      xf j (finitePathPrev (Fin.last m) hm0) := by
    rw [finitePathNatLift_of_lt (i := m - 1) (xf j) (by omega), hprevEq]
  have hxLastLift : finitePathNatLift (xf j) m = xf j (Fin.last m) := by
    rw [finitePathNatLift_of_lt (i := m) (xf j) (by omega), hlastEq]
  have hboundary :
      1 + g + h -
          (h * weight ((S.gap j).idx
              (finitePathPrev (Fin.last m) hm0)) *
              xf j (finitePathPrev (Fin.last m) hm0) -
            (g + h) * xf j (Fin.last m)) =
        1 + g + h -
          (h * finitePathNatLift ((S.gap j).gapS weight) (m - 1) *
              finitePathNatLift (xf j) (m - 1) -
            (g + h) * finitePathNatLift (xf j) m) := by
    rw [hsLift, hxPrevLift, hxLastLift]
  have hcoreRaw := hboundary.trans hcore
  have hexpand := S.forkSchurSelf_sub_next_eq_right_core_add_following
    weight p q e rho xf yw j hm0 hnext hunit
  have hAr : ∀ i, 0 ≤ (S.gap r).gapA p e i :=
    (S.gap r).gapA_nonneg (fun a => le_of_lt (hp a)) he
  have hcr : ∀ i, 0 ≤ (S.gap r).gapC weight q e rho i :=
    (S.gap r).gapC_nonneg (fun a => le_of_lt (hq a)) he hrho hw
  have hsr : ∀ i, 1 ≤ (S.gap r).gapS weight i :=
    (S.gap r).gapS_one_le hw
  have hscaleR : 1 ≤ (weight (S.fork r) : ℝ) := by
    exact_mod_cast hw (S.fork r)
  have hk : 0 ≤ k := le_of_lt (mul_pos (hq _)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw _) (he _)))
  have hxfR : ∀ i,
      ∑ t, finiteSourcePathMatrix ((S.gap r).gapA p e)
          ((S.gap r).gapC weight q e rho) ((S.gap r).gapS weight) i t * xf r t =
        sourceWrapForwardForcing ((S.gap r).gapA p e)
          ((S.gap r).gapC weight q e rho) i := by
    intro i
    rw [← (S.gap r).restrictedCurrentMatrix_eq_finiteSourcePathMatrix]
    exact hxf r i
  have hywR : ∀ i,
      ∑ t, finiteSourcePathMatrix ((S.gap r).gapA p e)
          ((S.gap r).gapC weight q e rho) ((S.gap r).gapS weight) i t * yw r t =
        sourceWrapLeftForcing ((S.gap r).gapA p e)
          (weight (S.fork r)) i := by
    intro i
    rw [← (S.gap r).restrictedCurrentMatrix_eq_finiteSourcePathMatrix]
    exact hyw r i
  have hfollow := finiteSourcePath_literal_following_budget_nonneg hnext
    ((S.gap r).gapA p e) ((S.gap r).gapC weight q e rho)
    ((S.gap r).gapS weight) (xf r) (yw r) hAr hcr hsr hscaleR hk
    (by simpa [SourceGapEmbedding.gapS, r, mr] using hnextUnit) hxfR hywR
  dsimp [r, m, kLeft, g, h] at hcoreRaw ⊢
  dsimp [r, m, g, h, k] at hexpand hfollow
  rw [hexpand]
  linarith [hcoreRaw]

/-- The right-core lower bound at a two-coordinate gap.  This is the endpoint
collision companion to `right_core_le_forkSchurSelf_sub_next`; the condensed
formula is identical once the first/penultimate forcing is stated correctly. -/
theorem two_coordinate_right_core_le_forkSchurSelf_sub_next
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : S.gapLength j = 1)
    (hnext : 0 < S.gapLength (S.step j))
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hnextUnit : weight ((S.gap (S.step j)).idx
      (Fin.last (S.gapLength (S.step j)))) = 1)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i) :
    let r := S.step j
    let kLeft := q (S.fork j) *
      (sourceForkNextCoeff next weight back rho (S.fork j) /
        e (next (S.fork j)))
    let g := p (S.fork r) / e (S.fork r)
    let h := q (S.fork r) *
      (sourceForkBackCoeff next weight back rho (S.fork r)
        ((S.gap j).idx (Fin.last (S.gapLength j))) /
          e ((S.gap j).idx (Fin.last (S.gapLength j))))
    let eff := (S.gap j).properWrapState weight p q e rho
      (weight (S.fork j)) kLeft
    let Aeff := wrapCondensedA eff.A
      (finitePathNatLift ((S.gap j).gapA p e) (S.gapLength j))
      (finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1))
    let heff := wrapCondensedH eff.A
      (finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) h
    let d := 1 + Aeff +
      finitePathNatLift ((S.gap j).gapC weight q e rho) (S.gapLength j)
    (d + g + heff) / d ≤
      S.forkSchurSelfCoefficient weight p q e rho xf yw r -
        S.forkSchurNextCoefficient weight p q e rho xf r := by
  let r := S.step j
  let m := S.gapLength j
  let mr := S.gapLength r
  let kLeft := q (S.fork j) *
    (sourceForkNextCoeff next weight back rho (S.fork j) /
      e (next (S.fork j)))
  let g := p (S.fork r) / e (S.fork r)
  let h := q (S.fork r) *
    (sourceForkBackCoeff next weight back rho (S.fork r)
      ((S.gap j).idx (Fin.last m)) / e ((S.gap j).idx (Fin.last m)))
  let k := q (S.fork r) *
    (sourceForkNextCoeff next weight back rho (S.fork r) /
      e (next (S.fork r)))
  have hscaleLeft : 0 < (weight (S.fork j) : ℝ) := by
    exact_mod_cast hw (S.fork j)
  have hkLeft : 0 < kLeft := mul_pos (hq _)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw _) (he _))
  have hxf0 :
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho 0 t * xf j t =
        (S.gap j).gapC weight q e rho 0 := by
    simpa [sourceWrapForwardForcing, m, hm] using hxf j 0
  have hxfLast :
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho
          (Fin.last m) t * xf j t =
        -((S.gap j).gapA p e (Fin.last m) +
          (S.gap j).gapC weight q e rho (Fin.last m)) := by
    simpa [sourceWrapForwardForcing, m, hm] using hxf j (Fin.last m)
  have hcore := (S.gap j).restricted_two_coordinate_right_diagonal_core_eq
    hm weight p q e rho (xf j) hp hq he hrho hw
    (by simpa [SourceGapEmbedding.gapS] using hunit) hxf0 hxfLast
    (scale := (weight (S.fork j) : ℝ)) (k := kLeft) (h := h) (g := g)
  have hm0 : 0 < m := by omega
  have hprevEq :
      (⟨m - 1, by omega⟩ : Fin (m + 1)) =
        finitePathPrev (Fin.last m) hm0 := by
    apply Fin.ext
    simp [finitePathPrev]
  have hlastEq : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := by
    apply Fin.ext
    simp
  have hsLift :
      finitePathNatLift ((S.gap j).gapS weight) (m - 1) =
        (weight ((S.gap j).idx
          (finitePathPrev (Fin.last m) hm0)) : ℝ) := by
    rw [finitePathNatLift_of_lt (i := m - 1)
      ((S.gap j).gapS weight) (by omega), hprevEq]
    rfl
  have hxPrevLift : finitePathNatLift (xf j) (m - 1) =
      xf j (finitePathPrev (Fin.last m) hm0) := by
    rw [finitePathNatLift_of_lt (i := m - 1) (xf j) (by omega), hprevEq]
  have hxLastLift : finitePathNatLift (xf j) m = xf j (Fin.last m) := by
    rw [finitePathNatLift_of_lt (i := m) (xf j) (by omega), hlastEq]
  have hboundary :
      1 + g + h -
          (h * weight ((S.gap j).idx
              (finitePathPrev (Fin.last m) hm0)) *
              xf j (finitePathPrev (Fin.last m) hm0) -
            (g + h) * xf j (Fin.last m)) =
        1 + g + h -
          (h * finitePathNatLift ((S.gap j).gapS weight) (m - 1) *
              finitePathNatLift (xf j) (m - 1) -
            (g + h) * finitePathNatLift (xf j) m) := by
    rw [hsLift, hxPrevLift, hxLastLift]
  have hcoreRaw := hboundary.trans hcore
  have hexpand := S.forkSchurSelf_sub_next_eq_right_core_add_following
    weight p q e rho xf yw j (by omega) hnext hunit
  have hAr : ∀ i, 0 ≤ (S.gap r).gapA p e i :=
    (S.gap r).gapA_nonneg (fun a => le_of_lt (hp a)) he
  have hcr : ∀ i, 0 ≤ (S.gap r).gapC weight q e rho i :=
    (S.gap r).gapC_nonneg (fun a => le_of_lt (hq a)) he hrho hw
  have hsr : ∀ i, 1 ≤ (S.gap r).gapS weight i :=
    (S.gap r).gapS_one_le hw
  have hscaleR : 1 ≤ (weight (S.fork r) : ℝ) := by
    exact_mod_cast hw (S.fork r)
  have hk : 0 ≤ k := le_of_lt (mul_pos (hq _)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw _) (he _)))
  have hxfR : ∀ i,
      ∑ t, finiteSourcePathMatrix ((S.gap r).gapA p e)
          ((S.gap r).gapC weight q e rho) ((S.gap r).gapS weight) i t * xf r t =
        sourceWrapForwardForcing ((S.gap r).gapA p e)
          ((S.gap r).gapC weight q e rho) i := by
    intro i
    rw [← (S.gap r).restrictedCurrentMatrix_eq_finiteSourcePathMatrix]
    exact hxf r i
  have hywR : ∀ i,
      ∑ t, finiteSourcePathMatrix ((S.gap r).gapA p e)
          ((S.gap r).gapC weight q e rho) ((S.gap r).gapS weight) i t * yw r t =
        sourceWrapLeftForcing ((S.gap r).gapA p e)
          (weight (S.fork r)) i := by
    intro i
    rw [← (S.gap r).restrictedCurrentMatrix_eq_finiteSourcePathMatrix]
    exact hyw r i
  have hfollow := finiteSourcePath_literal_following_budget_nonneg hnext
    ((S.gap r).gapA p e) ((S.gap r).gapC weight q e rho)
    ((S.gap r).gapS weight) (xf r) (yw r) hAr hcr hsr hscaleR hk
    (by simpa [SourceGapEmbedding.gapS, r, mr] using hnextUnit) hxfR hywR
  dsimp [r, m, kLeft, g, h] at hcoreRaw ⊢
  dsimp [r, m, g, h, k] at hexpand hfollow
  rw [hexpand]
  linarith [hcoreRaw]

/-- The genuine fork diagonal strictly dominates its successor Schur port
whenever the current and following literal gaps are positive. -/
theorem forkSchurSelf_sub_next_pos
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hnext : 0 < S.gapLength (S.step j))
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hnextUnit : weight ((S.gap (S.step j)).idx
      (Fin.last (S.gapLength (S.step j)))) = 1)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * yw a t =
        sourceWrapLeftForcing ((S.gap a).gapA p e)
          (weight (S.fork a)) i) :
    0 < S.forkSchurSelfCoefficient weight p q e rho xf yw (S.step j) -
      S.forkSchurNextCoefficient weight p q e rho xf (S.step j) := by
  let r := S.step j
  let m := S.gapLength j
  let kLeft := q (S.fork j) *
    (sourceForkNextCoeff next weight back rho (S.fork j) /
      e (next (S.fork j)))
  let g := p (S.fork r) / e (S.fork r)
  let h := q (S.fork r) *
    (sourceForkBackCoeff next weight back rho (S.fork r)
      ((S.gap j).idx (Fin.last m)) / e ((S.gap j).idx (Fin.last m)))
  let eff := (S.gap j).properWrapState weight p q e rho
    (weight (S.fork j)) kLeft
  let Aeff := wrapCondensedA eff.A
    (finitePathNatLift ((S.gap j).gapA p e) m)
    (finitePathNatLift ((S.gap j).gapC weight q e rho) (m - 1))
    (finitePathNatLift ((S.gap j).gapS weight) (m - 1))
  let heff := wrapCondensedH eff.A
    (finitePathNatLift ((S.gap j).gapC weight q e rho) (m - 1))
    (finitePathNatLift ((S.gap j).gapS weight) (m - 1)) h
  let d := 1 + Aeff +
    finitePathNatLift ((S.gap j).gapC weight q e rho) m
  have hcore : (d + g + heff) / d ≤
      S.forkSchurSelfCoefficient weight p q e rho xf yw r -
        S.forkSchurNextCoefficient weight p q e rho xf r := by
    by_cases hm1 : S.gapLength j = 1
    · exact S.two_coordinate_right_core_le_forkSchurSelf_sub_next
        weight p q e rho xf yw j hm1 hnext hp hq he hrho hw
        hunit hnextUnit hxf hyw
    · exact S.right_core_le_forkSchurSelf_sub_next
        weight p q e rho xf yw j (by omega) hnext hp hq he hrho hw
        hunit hnextUnit hxf hyw
  let An := finitePathNatLift ((S.gap j).gapA p e)
  let cn := finitePathNatLift ((S.gap j).gapC weight q e rho)
  let sn := finitePathNatLift ((S.gap j).gapS weight)
  have hAn : ∀ i, 0 < An i := fun i => div_pos (hp _) (he _)
  have hcn : ∀ i, 0 < cn i := by
    intro i
    unfold cn finitePathNatLift SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  have hsn : ∀ i, 0 < sn i := fun i => (S.gap j).gapS_pos hw _
  have hscale : 0 < (weight (S.fork j) : ℝ) := by
    exact_mod_cast hw (S.fork j)
  have hkLeft : 0 < kLeft := mul_pos (hq _)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw _) (he _))
  have heffPos : eff.StrictlyPositive := by
    simpa [eff, SourceGapEmbedding.properWrapState, An, cn, sn, m] using
      (natWrapPrefixState_pos An cn sn hAn hcn hsn hscale hkLeft (m - 1))
  have hh : 0 < h := mul_pos (hq _)
    (div_pos (sourceForkBackCoeff_pos next weight back hrho _ _)
      (he _))
  have hparams := wrap_condensed_parameters_pos heffPos.1 (hAn m)
    (hcn (m - 1)) (hsn (m - 1)) heffPos.2.1 heffPos.2.2 hh
  have hd : 0 < d := by
    dsimp [d, Aeff, m, cn] at hparams ⊢
    linarith [hparams.1, hcn (S.gapLength j)]
  have hg : 0 < g := div_pos (hp _) (he _)
  have hquot : 0 < (d + g + heff) / d := by
    apply div_pos
    · dsimp [heff, eff, m, cn, sn] at hparams ⊢
      linarith [hparams.2.2.2]
    · exact hd
  dsimp [r] at hcore ⊢
  exact lt_of_lt_of_le hquot hcore

/-- Exact bookkeeping for the left diagonal at a literal fork.  The current
gap supplies the grouped local term, while the preceding gap appears only
through its correction minus the direct back/degradation budget. -/
theorem forkSchurSelf_eq_left_group_add_preceding_budget
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) :
    let pred := S.step.symm j
    let last := Fin.last (S.gapLength pred)
    let g := p (S.fork j) / e (S.fork j)
    let h := q (S.fork j) *
      (sourceForkBackCoeff next weight back rho (S.fork j)
        ((S.gap pred).idx last) / e ((S.gap pred).idx last))
    let k := q (S.fork j) *
      (sourceForkNextCoeff next weight back rho (S.fork j) /
        e (next (S.fork j)))
    let precedingCorrection := ∑ i,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e
          (S.fork j) ((S.gap pred).idx i) * xf pred i
    S.forkSchurSelfCoefficient weight p q e rho xf yw j =
      (1 + k * weight (S.fork j) + k * yw j 0) +
        (g + h - precedingCorrection) := by
  let pred := S.step.symm j
  let last : Fin (S.gapLength pred + 1) := Fin.last (S.gapLength pred)
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  let g := p (S.fork j) / e (S.fork j)
  let h := q (S.fork j) *
    (sourceForkBackCoeff next weight back rho (S.fork j)
      ((S.gap pred).idx last) / e ((S.gap pred).idx last))
  let k := q (S.fork j) *
    (sourceForkNextCoeff next weight back rho (S.fork j) /
      e (next (S.fork j)))
  have hdiag := sourceOrderedCurrentMatrix_fork_diagonal
    next weight back (p := p) (q := q) (e := e) (rho := rho)
    (r := S.fork j) (z := (S.gap pred).idx last)
    (by simpa [pred, last] using (S.wrap pred).pre.fork_back)
    (by simpa [pred, last] using
      (S.wrap pred).pre.terminal_ne_fork_successor)
    (by simpa [pred] using (S.wrap pred).pre.fork_ne_next)
    (by simpa [pred, last] using (S.wrap pred).pre.terminal_ne_fork)
  have hpost := (S.wrap j).post.fork_postGap_mul
    weight p q e rho (yw j)
  change M (S.fork j) (S.fork j) = _ at hdiag
  change (∑ i, M (S.fork j) ((S.gap j).idx i) * yw j i) = _ at hpost
  simp only [forkSchurSelfCoefficient]
  change M (S.fork j) (S.fork j) -
      (∑ i, M (S.fork j) ((S.gap pred).idx i) * xf pred i) -
      (∑ i, M (S.fork j) ((S.gap j).idx i) * yw j i) = _
  rw [hdiag, hpost]
  dsimp [g, h, k, pred, last]
  ring

/-- If the preceding mixed response consumes no more than its direct fork
budget, the genuine literal Schur diagonal is at least the condensed left
core of the current gap. -/
theorem left_core_le_forkSchurSelf
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hyw : ∀ i,
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t * yw j t =
        sourceWrapLeftForcing ((S.gap j).gapA p e)
          (weight (S.fork j)) i)
    (hpreceding :
      let pred := S.step.symm j
      let last := Fin.last (S.gapLength pred)
      ∑ i,
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            (S.fork j) ((S.gap pred).idx i) * xf pred i ≤
        p (S.fork j) / e (S.fork j) +
          q (S.fork j) *
            (sourceForkBackCoeff next weight back rho (S.fork j)
              ((S.gap pred).idx last) / e ((S.gap pred).idx last))) :
    let k := q (S.fork j) *
      (sourceForkNextCoeff next weight back rho (S.fork j) /
        e (next (S.fork j)))
    let eff := (S.gap j).properWrapState weight p q e rho
      (weight (S.fork j)) k
    let Aeff := wrapCondensedA eff.A
      (finitePathNatLift ((S.gap j).gapA p e) (S.gapLength j))
      (finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1))
    let seff := wrapCondensedScale eff.A
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) eff.scale
    let keff := wrapCondensedK eff.A
      (finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) eff.k
    let d := 1 + Aeff +
      finitePathNatLift ((S.gap j).gapC weight q e rho) (S.gapLength j)
    (d + keff * seff *
      (1 + finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j))) / d ≤
      S.forkSchurSelfCoefficient weight p q e rho xf yw j := by
  let k := q (S.fork j) *
    (sourceForkNextCoeff next weight back rho (S.fork j) /
      e (next (S.fork j)))
  have hscale : 0 < (weight (S.fork j) : ℝ) := by
    exact_mod_cast hw (S.fork j)
  have hk : 0 < k := mul_pos (hq _)
    (div_pos (sourceForkNextCoeff_pos next weight back hrho hw _) (he _))
  have hywEq : ∀ i,
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t * yw j t =
        if i.val = 0 then
          -((S.gap j).gapA p e i * (weight (S.fork j) : ℝ)) else 0 := by
    intro i
    simpa [sourceWrapLeftForcing] using hyw i
  have hlocal := (S.gap j).restricted_left_diagonal_core_le hm
    weight p q e rho (yw j) hp hq he hrho hw hscale hk
    (by simpa [SourceGapEmbedding.gapS] using hunit) hywEq
  have hexpand := S.forkSchurSelf_eq_left_group_add_preceding_budget
    weight p q e rho xf yw j
  dsimp [k] at hlocal ⊢
  dsimp only at hpreceding
  dsimp at hexpand
  rw [hexpand]
  linarith

/-- The abstract preceding-budget premise in `left_core_le_forkSchurSelf`
is automatic for a literal positive preceding gap by the terminal-basis
shift.  Singleton preceding gaps are deliberately left to the weak-gap
splice, avoiding dependent casts in the long-gap interface. -/
theorem literal_positive_preceding_left_core_le_forkSchurSelf
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : ∀ a : Fin l, Fin (S.gapLength a + 1) → ℝ)
    (j : Fin l) (hm : 0 < S.gapLength j)
    (hpred : 0 < S.gapLength (S.step.symm j))
    (JFork : ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (he : ∀ a, 0 < e a) (hrho : ∀ a, 0 < rho a)
    (hw : ∀ a, 0 < weight a) (hJFork : 0 < JFork)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (hpredUnit :
      weight ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j)))) = 1)
    (horder :
      ((S.gap (S.step.symm j)).idx
        (Fin.last (S.gapLength (S.step.symm j)))).val <
          (next (S.fork j)).val)
    (hpFork : p (S.fork j) = q (S.fork j) + JFork)
    (hpLast :
      p ((S.gap (S.step.symm j)).idx
          (Fin.last (S.gapLength (S.step.symm j)))) =
        q ((S.gap (S.step.symm j)).idx
            (Fin.last (S.gapLength (S.step.symm j)))) +
          e (S.fork j) + JFork)
    (hxf : ∀ a i,
      ∑ t, (S.gap a).restrictedCurrentMatrix weight p q e rho i t * xf a t =
        sourceWrapForwardForcing ((S.gap a).gapA p e)
          ((S.gap a).gapC weight q e rho) i)
    (hyw : ∀ i,
      ∑ t, (S.gap j).restrictedCurrentMatrix weight p q e rho i t * yw j t =
        sourceWrapLeftForcing ((S.gap j).gapA p e)
          (weight (S.fork j)) i) :
    let k := q (S.fork j) *
      (sourceForkNextCoeff next weight back rho (S.fork j) /
        e (next (S.fork j)))
    let eff := (S.gap j).properWrapState weight p q e rho
      (weight (S.fork j)) k
    let Aeff := wrapCondensedA eff.A
      (finitePathNatLift ((S.gap j).gapA p e) (S.gapLength j))
      (finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1))
    let seff := wrapCondensedScale eff.A
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) eff.scale
    let keff := wrapCondensedK eff.A
      (finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j - 1))
      (finitePathNatLift ((S.gap j).gapS weight) (S.gapLength j - 1)) eff.k
    let d := 1 + Aeff +
      finitePathNatLift ((S.gap j).gapC weight q e rho) (S.gapLength j)
    (d + keff * seff *
      (1 + finitePathNatLift ((S.gap j).gapC weight q e rho)
        (S.gapLength j))) / d ≤
      S.forkSchurSelfCoefficient weight p q e rho xf yw j := by
  let pred := S.step.symm j
  have hpreceding :
      ∑ i,
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
            (S.fork j) ((S.gap pred).idx i) * xf pred i ≤
        p (S.fork j) / e (S.fork j) +
          q (S.fork j) *
            (sourceForkBackCoeff next weight back rho (S.fork j)
              ((S.gap pred).idx (Fin.last (S.gapLength pred))) /
                e ((S.gap pred).idx (Fin.last (S.gapLength pred)))) := by
    have hpos := (S.wrap pred).pre.forward_correction_le_direct_of_nonwrap
      (by simpa [pred] using hpred) weight p q e rho JFork
      (by simpa [pred] using hpredUnit)
      (by simpa [pred] using horder)
      (by simpa [pred] using hpFork)
      (by simpa [pred] using hpLast)
      hp hq he hrho hw hJFork (xf pred)
      (by intro i; exact hxf pred i)
    simpa only [pred, Equiv.apply_symm_apply] using hpos
  exact S.left_core_le_forkSchurSelf weight p q e rho xf yw j hm
    hp hq he hrho hw hunit hyw (by simpa [pred] using hpreceding)

end SourceCyclicNonemptyGapSystem

end TypeIIL

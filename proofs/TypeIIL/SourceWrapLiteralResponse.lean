import proofs.TypeIIL.SourceWrapEndpointBudget
import proofs.TypeIIL.SourceWrapFiniteMargin

namespace TypeIIL

open scoped BigOperators

/-- Literal long-gap response adapter.  The two restricted source columns
have exactly the mixed endpoint forcing dictated by the source entry ledger:
the right-fork column is positive at the penultimate row and negative at the
terminal row, while the left/wrap column is forced only at the first row.
Proper-prefix elimination turns those literal equations into the two-node
response equations consumed by the coupled raw-margin theorem. -/
theorem SourceGapEmbedding.restricted_response_raw_two_edge_margin
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (hm : 1 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf yw : Fin (m + 1) → ℝ) {scale k h g X Bprev Fprev W : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 < scale) (hk : 0 < k)
    (hunit : G.gapS weight (Fin.last m) = 1)
    (hh : 0 < h) (hg : 0 ≤ g)
    {followingBudget precedingCorrection : ℝ}
    (hfollowing : 0 ≤ followingBudget)
    (hpreceding : precedingCorrection ≤ 0)
    (hX :
      let eff := G.properWrapState weight p q e rho scale k
      let Aeff := wrapCondensedA eff.A (finitePathNatLift (G.gapA p e) m)
        (finitePathNatLift (G.gapC weight q e rho) (m - 1))
        (finitePathNatLift (G.gapS weight) (m - 1))
      let heffR := wrapCondensedH eff.A
        (finitePathNatLift (G.gapC weight q e rho) (m - 1))
        (finitePathNatLift (G.gapS weight) (m - 1)) h
      let d := 1 + Aeff + finitePathNatLift (G.gapC weight q e rho) m
      X = (d + g + heffR) / d + followingBudget)
    (hBprev :
      let eff := G.properWrapState weight p q e rho scale k
      let Aeff := wrapCondensedA eff.A (finitePathNatLift (G.gapA p e) m)
        (finitePathNatLift (G.gapC weight q e rho) (m - 1))
        (finitePathNatLift (G.gapS weight) (m - 1))
      let seff := wrapCondensedScale eff.A
        (finitePathNatLift (G.gapS weight) (m - 1)) eff.scale
      let keff := wrapCondensedK eff.A
        (finitePathNatLift (G.gapC weight q e rho) (m - 1))
        (finitePathNatLift (G.gapS weight) (m - 1)) eff.k
      let d := 1 + Aeff + finitePathNatLift (G.gapC weight q e rho) m
      Bprev = (d + keff * seff *
        (1 + finitePathNatLift (G.gapC weight q e rho) m)) / d -
          precedingCorrection)
    (hxf_first :
      ∑ j, G.restrictedCurrentMatrix weight p q e rho 0 j * xf j = 0)
    (hxf_rows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m - 1 →
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j = 0)
    (hxf_penultimate :
      ∑ j, G.restrictedCurrentMatrix weight p q e rho
        ⟨m - 1, by omega⟩ j * xf j =
          G.gapC weight q e rho ⟨m - 1, by omega⟩)
    (hxf_terminal :
      ∑ j, G.restrictedCurrentMatrix weight p q e rho (Fin.last m) j * xf j =
        -(G.gapA p e (Fin.last m) +
          G.gapC weight q e rho (Fin.last m)))
    (hyw_first :
      ∑ j, G.restrictedCurrentMatrix weight p q e rho 0 j * yw j =
        -(G.gapA p e 0 * scale))
    (hyw_rows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m - 1 →
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j = 0)
    (hyw_penultimate :
      ∑ j, G.restrictedCurrentMatrix weight p q e rho
        ⟨m - 1, by omega⟩ j * yw j = 0)
    (hyw_terminal :
      ∑ j, G.restrictedCurrentMatrix weight p q e rho (Fin.last m) j * yw j = 0)
    (hFprev :
      let eff := G.properWrapState weight p q e rho scale k
      Fprev = eff.k * finitePathNatLift xf (m - 1))
    (hW : W = -(h * finitePathNatLift (G.gapS weight) (m - 1) *
          finitePathNatLift yw (m - 1) -
        (g + h) * finitePathNatLift yw m)) :
    W * Fprev < X * Bprev := by
  let An := finitePathNatLift (G.gapA p e)
  let cn := finitePathNatLift (G.gapC weight q e rho)
  let sn := finitePathNatLift (G.gapS weight)
  let eff := natWrapPrefixState An cn sn scale k (m - 1)
  let penultimate : Fin (m + 1) := ⟨m - 1, by omega⟩
  let terminal : Fin (m + 1) := Fin.last m
  have hA : ∀ i, 0 < An i := fun i => div_pos (hp _) (he _)
  have hc : ∀ i, 0 < cn i := by
    intro i
    unfold cn finitePathNatLift SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  have hs : ∀ i, 0 < sn i := fun i => G.gapS_pos hw _
  have hforward₀ :
      wrapPrefixPivot eff.A (cn (m - 1)) (sn (m - 1)) *
          finitePathNatLift xf (m - 1) -
        cn (m - 1) * finitePathNatLift xf m = cn (m - 1) := by
    have hfirst :
        ∑ j, G.restrictedCurrentMatrix weight p q e rho 0 j * xf j =
          G.gapA p e 0 * scale * 0 := by simpa using hxf_first
    have hx := G.restricted_properPrefixEquation_final_rhs hm weight p q e rho xf
      hp hq he hrho hw hscale hk hfirst hxf_rows hxf_penultimate
    dsimp only [SourceGapEmbedding.properWrapState, An, cn, sn, eff]
    rw [finitePathNatLift_of_lt (i := m - 1)
      (G.gapC weight q e rho) (by omega)] at hx ⊢
    unfold wrapPrefixPivot
    linarith
  have hwrap₀ :
      wrapPrefixPivot eff.A (cn (m - 1)) (sn (m - 1)) *
          finitePathNatLift yw (m - 1) -
        cn (m - 1) * finitePathNatLift yw m = -(eff.A * eff.scale) := by
    have hfirst :
        ∑ j, G.restrictedCurrentMatrix weight p q e rho 0 j * yw j =
          G.gapA p e 0 * scale * (-1) := by
      simpa only [mul_neg, mul_one] using hyw_first
    have hy := G.restricted_properPrefixEquation_final_rhs hm weight p q e rho yw
      hp hq he hrho hw hscale hk hfirst hyw_rows hyw_penultimate
      (scale := scale) (k := k) (L := -1) (rhs := 0)
    dsimp only [SourceGapEmbedding.properWrapState, An, cn, sn, eff]
    unfold wrapPrefixPivot
    linarith
  have hforward₁ :
      -(An m * sn (m - 1)) * finitePathNatLift xf (m - 1) +
        (1 + An m + cn m) * finitePathNatLift xf m = -(An m + cn m) := by
    rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hxf_terminal
    rw [finiteSourcePathMatrix_mul_apply] at hxf_terminal
    have hm0 : 0 < m := by omega
    simp only [Fin.val_last, hm0, dite_true, lt_self_iff_false, dite_false] at hxf_terminal
    have hprev : finitePathPrev (Fin.last m) hm0 = penultimate := by
      apply Fin.ext
      simp [finitePathPrev, penultimate]
    rw [hprev] at hxf_terminal
    rw [hunit] at hxf_terminal
    simp only [An, cn, sn, finitePathNatLift_of_lt (i := m) (G.gapA p e) (by omega),
      finitePathNatLift_of_lt (i := m - 1) (G.gapS weight) (by omega),
      finitePathNatLift_of_lt (i := m - 1) xf (by omega),
      finitePathNatLift_of_lt (i := m) (G.gapC weight q e rho) (by omega),
      finitePathNatLift_of_lt (i := m) xf (by omega)]
    have hlast : (Fin.last m : Fin (m + 1)) = ⟨m, by omega⟩ := by
      apply Fin.ext
      simp
    have hpen : penultimate = ⟨m - 1, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hlast, hpen] at hxf_terminal
    linear_combination hxf_terminal
  have hwrap₁ :
      -(An m * sn (m - 1)) * finitePathNatLift yw (m - 1) +
        (1 + An m + cn m) * finitePathNatLift yw m = 0 := by
    rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hyw_terminal
    rw [finiteSourcePathMatrix_mul_apply] at hyw_terminal
    have hm0 : 0 < m := by omega
    simp only [Fin.val_last, hm0, dite_true, lt_self_iff_false, dite_false] at hyw_terminal
    have hprev : finitePathPrev (Fin.last m) hm0 = penultimate := by
      apply Fin.ext
      simp [finitePathPrev, penultimate]
    rw [hprev] at hyw_terminal
    rw [hunit] at hyw_terminal
    simp only [An, cn, sn, finitePathNatLift_of_lt (i := m) (G.gapA p e) (by omega),
      finitePathNatLift_of_lt (i := m - 1) (G.gapS weight) (by omega),
      finitePathNatLift_of_lt (i := m - 1) yw (by omega),
      finitePathNatLift_of_lt (i := m) (G.gapC weight q e rho) (by omega),
      finitePathNatLift_of_lt (i := m) yw (by omega)]
    have hlast : (Fin.last m : Fin (m + 1)) = ⟨m, by omega⟩ := by
      apply Fin.ext
      simp
    have hpen : penultimate = ⟨m - 1, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hlast, hpen] at hyw_terminal
    linear_combination hyw_terminal
  apply natWrapPrefix_response_raw_two_edge_margin_of_endpoint_budgets
    An cn sn (m - 1) hA hc hs hscale hk (hA m) (hc (m - 1))
      (hs (m - 1)) (hc m) hh hg hfollowing hpreceding
  · simpa only [SourceGapEmbedding.properWrapState, An, cn, sn, eff] using hX
  · simpa only [SourceGapEmbedding.properWrapState, An, cn, sn, eff] using hBprev
  · exact hforward₀
  · exact hforward₁
  · simpa only [SourceGapEmbedding.properWrapState, An, cn, sn, eff] using hFprev
  · exact hwrap₀
  · exact hwrap₁
  · simpa only [sn] using hW

/-- The two-internal-reaction boundary case.  Here the proper prefix is
empty, so the four response equations are read directly from the two literal
path rows. -/
theorem finiteSourcePath_two_node_response_raw_two_edge_margin
    (A c s xf yw : Fin 2 → ℝ) {scale k h g X Bprev Fprev W : ℝ}
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i) (hs : ∀ i, 0 < s i)
    (hterminalUnit : s 1 = 1)
    (hscale : 0 < scale) (hk : 0 < k) (hh : 0 < h) (hg : 0 ≤ g)
    {followingBudget precedingCorrection : ℝ}
    (hfollowing : 0 ≤ followingBudget)
    (hpreceding : precedingCorrection ≤ 0)
    (hX :
      let eff := natWrapPrefixState (finitePathNatLift A)
        (finitePathNatLift c) (finitePathNatLift s) scale k 0
      let Aeff := wrapCondensedA eff.A (finitePathNatLift A 1)
        (finitePathNatLift c 0) (finitePathNatLift s 0)
      let heffR := wrapCondensedH eff.A (finitePathNatLift c 0)
        (finitePathNatLift s 0) h
      let d := 1 + Aeff + finitePathNatLift c 1
      X = (d + g + heffR) / d + followingBudget)
    (hBprev :
      let eff := natWrapPrefixState (finitePathNatLift A)
        (finitePathNatLift c) (finitePathNatLift s) scale k 0
      let Aeff := wrapCondensedA eff.A (finitePathNatLift A 1)
        (finitePathNatLift c 0) (finitePathNatLift s 0)
      let seff := wrapCondensedScale eff.A (finitePathNatLift s 0) eff.scale
      let keff := wrapCondensedK eff.A (finitePathNatLift c 0)
        (finitePathNatLift s 0) eff.k
      let d := 1 + Aeff + finitePathNatLift c 1
      Bprev = (d + keff * seff * (1 + finitePathNatLift c 1)) / d -
        precedingCorrection)
    (hxf₀ : ∑ j, finiteSourcePathMatrix A c s 0 j * xf j = c 0)
    (hxf₁ : ∑ j, finiteSourcePathMatrix A c s 1 j * xf j =
      -(A 1 + c 1))
    (hyw₀ : ∑ j, finiteSourcePathMatrix A c s 0 j * yw j =
      -(A 0 * scale))
    (hyw₁ : ∑ j, finiteSourcePathMatrix A c s 1 j * yw j = 0)
    (hFprev :
      let eff := natWrapPrefixState (finitePathNatLift A)
        (finitePathNatLift c) (finitePathNatLift s) scale k 0
      Fprev = eff.k * finitePathNatLift xf 0)
    (hW : W = -(h * finitePathNatLift s 0 * finitePathNatLift yw 0 -
      (g + h) * finitePathNatLift yw 1)) :
    W * Fprev < X * Bprev := by
  let An := finitePathNatLift A
  let cn := finitePathNatLift c
  let sn := finitePathNatLift s
  have hAn : ∀ i, 0 < An i := fun i => hA _
  have hcn : ∀ i, 0 < cn i := fun i => hc _
  have hsn : ∀ i, 0 < sn i := fun i => hs _
  have hf₀ : wrapPrefixPivot (An 0) (cn 0) (sn 0) *
      finitePathNatLift xf 0 - cn 0 * finitePathNatLift xf 1 = cn 0 := by
    rw [finiteSourcePathMatrix_mul_apply] at hxf₀
    simp only [Fin.val_zero, lt_self_iff_false, dite_false,
      show (0 : ℕ) < 1 by omega, dite_true] at hxf₀
    dsimp only [An, cn, sn]
    rw [finitePathNatLift_of_lt (i := 0) A (by omega),
      finitePathNatLift_of_lt (i := 0) c (by omega),
      finitePathNatLift_of_lt (i := 0) s (by omega),
      finitePathNatLift_of_lt (i := 0) xf (by omega),
      finitePathNatLift_of_lt (i := 1) xf (by omega)]
    unfold wrapPrefixPivot
    simpa [finitePathNext, sub_eq_add_neg] using hxf₀
  have hf₁ : -(An 1 * sn 0) * finitePathNatLift xf 0 +
      (1 + An 1 + cn 1) * finitePathNatLift xf 1 = -(An 1 + cn 1) := by
    rw [finiteSourcePathMatrix_mul_apply] at hxf₁
    simp only [show (0 : ℕ) < 1 by omega, Fin.val_one, dite_true,
      lt_self_iff_false, dite_false] at hxf₁
    have hprev : ∀ hp : 0 < (1 : Fin 2).val,
        finitePathPrev (1 : Fin 2) hp = 0 := by
      intro hp
      apply Fin.ext
      simp [finitePathPrev]
    simp only [hprev] at hxf₁
    rw [hterminalUnit] at hxf₁
    dsimp only [An, cn, sn]
    rw [finitePathNatLift_of_lt (i := 1) A (by omega),
      finitePathNatLift_of_lt (i := 0) s (by omega),
      finitePathNatLift_of_lt (i := 0) xf (by omega),
      finitePathNatLift_of_lt (i := 1) c (by omega),
      finitePathNatLift_of_lt (i := 1) xf (by omega)]
    change -(A 1 * s 0) * xf 0 + (1 + A 1 + c 1) * xf 1 =
      -(A 1 + c 1)
    linarith
  have hw₀ : wrapPrefixPivot (An 0) (cn 0) (sn 0) *
      finitePathNatLift yw 0 - cn 0 * finitePathNatLift yw 1 =
        -(An 0 * scale) := by
    rw [finiteSourcePathMatrix_mul_apply] at hyw₀
    simp only [Fin.val_zero, lt_self_iff_false, dite_false,
      show (0 : ℕ) < 1 by omega, dite_true] at hyw₀
    dsimp only [An, cn, sn]
    rw [finitePathNatLift_of_lt (i := 0) A (by omega),
      finitePathNatLift_of_lt (i := 0) c (by omega),
      finitePathNatLift_of_lt (i := 0) s (by omega),
      finitePathNatLift_of_lt (i := 0) yw (by omega),
      finitePathNatLift_of_lt (i := 1) yw (by omega)]
    unfold wrapPrefixPivot
    simpa [finitePathNext, sub_eq_add_neg] using hyw₀
  have hw₁ : -(An 1 * sn 0) * finitePathNatLift yw 0 +
      (1 + An 1 + cn 1) * finitePathNatLift yw 1 = 0 := by
    rw [finiteSourcePathMatrix_mul_apply] at hyw₁
    simp only [show (0 : ℕ) < 1 by omega, Fin.val_one, dite_true,
      lt_self_iff_false, dite_false] at hyw₁
    have hprev : ∀ hp : 0 < (1 : Fin 2).val,
        finitePathPrev (1 : Fin 2) hp = 0 := by
      intro hp
      apply Fin.ext
      simp [finitePathPrev]
    simp only [hprev] at hyw₁
    rw [hterminalUnit] at hyw₁
    dsimp only [An, cn, sn]
    rw [finitePathNatLift_of_lt (i := 1) A (by omega),
      finitePathNatLift_of_lt (i := 0) s (by omega),
      finitePathNatLift_of_lt (i := 0) yw (by omega),
      finitePathNatLift_of_lt (i := 1) c (by omega),
      finitePathNatLift_of_lt (i := 1) yw (by omega)]
    change -(A 1 * s 0) * yw 0 + (1 + A 1 + c 1) * yw 1 = 0
    linarith
  apply natWrapPrefix_response_raw_two_edge_margin_of_endpoint_budgets
    An cn sn 0 hAn hcn hsn hscale hk (hAn 1) (hcn 0) (hsn 0)
      (hcn 1) hh hg hfollowing hpreceding
  · simpa only [An, cn, sn] using hX
  · simpa only [An, cn, sn] using hBprev
  · simpa only [natWrapPrefixState] using hf₀
  · exact hf₁
  · simpa only [An, cn, sn, natWrapPrefixState] using hFprev
  · simpa only [natWrapPrefixState] using hw₀
  · exact hw₁
  · simpa only [sn] using hW

/-- Exact forward Schur port for any literal positive gap. -/
theorem SourceGapEmbedding.literal_forward_flux_eq
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : Fin (m + 1) → ℝ) {scale k : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 < scale) (hk : 0 < k)
    (hunit : G.gapS weight (Fin.last m) = 1)
    (hxf : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
        if i.val = m - 1 then G.gapC weight q e rho i
        else if i.val = m then
          -(G.gapA p e i + G.gapC weight q e rho i)
        else 0) :
    let eff := G.properWrapState weight p q e rho scale k
    let Aeff := wrapCondensedA eff.A (finitePathNatLift (G.gapA p e) m)
      (finitePathNatLift (G.gapC weight q e rho) (m - 1))
      (finitePathNatLift (G.gapS weight) (m - 1))
    let keff := wrapCondensedK eff.A
      (finitePathNatLift (G.gapC weight q e rho) (m - 1))
      (finitePathNatLift (G.gapS weight) (m - 1)) eff.k
    let d := 1 + Aeff + finitePathNatLift (G.gapC weight q e rho) m
    eff.k * finitePathNatLift xf (m - 1) = keff / d := by
  let An := finitePathNatLift (G.gapA p e)
  let cn := finitePathNatLift (G.gapC weight q e rho)
  let sn := finitePathNatLift (G.gapS weight)
  let eff := natWrapPrefixState An cn sn scale k (m - 1)
  have hA : ∀ i, 0 < An i := fun i => div_pos (hp _) (he _)
  have hc : ∀ i, 0 < cn i := by
    intro i
    unfold cn finitePathNatLift SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  have hs : ∀ i, 0 < sn i := fun i => G.gapS_pos hw _
  have heff : eff.StrictlyPositive :=
    natWrapPrefixState_pos An cn sn hA hc hs hscale hk (m - 1)
  have hforward₀ :
      wrapPrefixPivot eff.A (cn (m - 1)) (sn (m - 1)) *
          finitePathNatLift xf (m - 1) -
        cn (m - 1) * finitePathNatLift xf m = cn (m - 1) := by
    by_cases hm1 : m = 1
    · subst m
      have h0 := hxf (0 : Fin 2)
      rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix,
        finiteSourcePathMatrix_mul_apply] at h0
      have hnext0 : ∀ hn : (0 : Fin 2).val < 1,
          finitePathNext (0 : Fin 2) hn = 1 := by
        intro hn
        apply Fin.ext
        simp [finitePathNext]
      simp only [hnext0] at h0
      simpa [An, cn, sn, eff, natWrapPrefixState,
        finitePathNatLift_of_lt, wrapPrefixPivot, sub_eq_add_neg] using h0
    · have hm2 : 1 < m := by omega
      have hfirst :
          ∑ j, G.restrictedCurrentMatrix weight p q e rho 0 j * xf j = 0 := by
        have hx := hxf 0
        have h0pen : (0 : ℕ) ≠ m - 1 := by omega
        have h0last : (0 : ℕ) ≠ m := by omega
        simpa [h0pen, h0last] using hx
      have hrows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m - 1 →
          ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j = 0 := by
        intro i hi him
        have hipen : i.val ≠ m - 1 := by omega
        have hilast : i.val ≠ m := by omega
        simpa [hipen, hilast] using hxf i
      have hpen :
          ∑ j, G.restrictedCurrentMatrix weight p q e rho
              ⟨m - 1, by omega⟩ j * xf j =
            G.gapC weight q e rho ⟨m - 1, by omega⟩ := by
        simpa using hxf ⟨m - 1, by omega⟩
      have hx := G.restricted_properPrefixEquation_final_rhs hm2
        weight p q e rho xf hp hq he hrho hw hscale hk
        (L := 0) (rhs := G.gapC weight q e rho ⟨m - 1, by omega⟩)
        (by simpa using hfirst) hrows hpen
      dsimp only [SourceGapEmbedding.properWrapState, An, cn, sn, eff]
      rw [finitePathNatLift_of_lt (i := m - 1)
        (G.gapC weight q e rho) (by omega)] at hx ⊢
      unfold wrapPrefixPivot
      linarith
  have hforward₁ :
      -(An m * sn (m - 1)) * finitePathNatLift xf (m - 1) +
        (1 + An m + cn m) * finitePathNatLift xf m = -(An m + cn m) := by
    have hx := hxf (Fin.last m)
    have hne : m ≠ m - 1 := by omega
    have hxterm :
        ∑ j, G.restrictedCurrentMatrix weight p q e rho (Fin.last m) j * xf j =
          -(G.gapA p e (Fin.last m) +
            G.gapC weight q e rho (Fin.last m)) := by
      simpa [hne] using hx
    rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix,
      finiteSourcePathMatrix_mul_apply] at hxterm
    simp only [Fin.val_last, hm, dite_true, lt_self_iff_false, dite_false] at hxterm
    have hprev : finitePathPrev (Fin.last m) hm = ⟨m - 1, by omega⟩ := by
      apply Fin.ext
      simp [finitePathPrev]
    rw [hprev, hunit] at hxterm
    simp only [An, cn, sn,
      finitePathNatLift_of_lt (i := m) (G.gapA p e) (by omega),
      finitePathNatLift_of_lt (i := m - 1) (G.gapS weight) (by omega),
      finitePathNatLift_of_lt (i := m - 1) xf (by omega),
      finitePathNatLift_of_lt (i := m) (G.gapC weight q e rho) (by omega),
      finitePathNatLift_of_lt (i := m) xf (by omega)]
    have hlast : (Fin.last m : Fin (m + 1)) = ⟨m, by omega⟩ := by
      apply Fin.ext
      simp
    rw [hlast] at hxterm
    linear_combination hxterm
  have hflux := wrapPrefixState_forward_flux_eq heff (hA m) (hc (m - 1))
    (hs (m - 1)) (hc m) hforward₀ hforward₁
  simpa only [SourceGapEmbedding.properWrapState, An, cn, sn, eff] using hflux

end TypeIIL

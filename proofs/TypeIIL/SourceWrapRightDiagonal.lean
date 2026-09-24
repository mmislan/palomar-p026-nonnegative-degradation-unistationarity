import proofs.TypeIIL.SourceWrapLiteralResponse

namespace TypeIIL

open scoped BigOperators

/-- Exact right-fork diagonal core after a literal long source gap is
condensed to its final two coordinates.  No sign is assigned to the mixed
response: its two terminal traces are combined with the direct diagonal. -/
theorem SourceGapEmbedding.restricted_right_diagonal_core_eq
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (hm : 1 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : Fin (m + 1) → ℝ) {scale k h g : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 < scale) (hk : 0 < k)
    (hunit : G.gapS weight (Fin.last m) = 1)
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
          G.gapC weight q e rho (Fin.last m))) :
    let eff := G.properWrapState weight p q e rho scale k
    let Aeff := wrapCondensedA eff.A (finitePathNatLift (G.gapA p e) m)
      (finitePathNatLift (G.gapC weight q e rho) (m - 1))
      (finitePathNatLift (G.gapS weight) (m - 1))
    let heff := wrapCondensedH eff.A
      (finitePathNatLift (G.gapC weight q e rho) (m - 1))
      (finitePathNatLift (G.gapS weight) (m - 1)) h
    let d := 1 + Aeff + finitePathNatLift (G.gapC weight q e rho) m
    1 + g + h -
        (h * finitePathNatLift (G.gapS weight) (m - 1) *
            finitePathNatLift xf (m - 1) -
          (g + h) * finitePathNatLift xf m) =
      (d + g + heff) / d := by
  let An := finitePathNatLift (G.gapA p e)
  let cn := finitePathNatLift (G.gapC weight q e rho)
  let sn := finitePathNatLift (G.gapS weight)
  let xfn := finitePathNatLift xf
  let eff := natWrapPrefixState An cn sn scale k (m - 1)
  have hAn : ∀ i, 0 < An i := fun i => div_pos (hp _) (he _)
  have hcn : ∀ i, 0 < cn i := by
    intro i
    unfold cn finitePathNatLift SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  have hsn : ∀ i, 0 < sn i := fun i => G.gapS_pos hw _
  have heffPos : eff.StrictlyPositive :=
    natWrapPrefixState_pos An cn sn hAn hcn hsn hscale hk (m - 1)
  have hforward₀ :
      wrapPrefixPivot eff.A (cn (m - 1)) (sn (m - 1)) * xfn (m - 1) -
          cn (m - 1) * xfn m = cn (m - 1) := by
    have hfirst :
        ∑ j, G.restrictedCurrentMatrix weight p q e rho 0 j * xf j =
          G.gapA p e 0 * scale * 0 := by simpa using hxf_first
    have hx := G.restricted_properPrefixEquation_final_rhs hm weight p q e rho xf
      hp hq he hrho hw hscale hk hfirst hxf_rows hxf_penultimate
    dsimp only [SourceGapEmbedding.properWrapState, An, cn, sn, xfn, eff]
    rw [finitePathNatLift_of_lt (i := m - 1)
      (G.gapC weight q e rho) (by omega)] at hx ⊢
    unfold wrapPrefixPivot
    linarith
  have hforward₁ :
      -(An m * sn (m - 1)) * xfn (m - 1) +
          (1 + An m + cn m) * xfn m = -(An m + cn m) := by
    rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hxf_terminal
    rw [finiteSourcePathMatrix_mul_apply] at hxf_terminal
    have hm0 : 0 < m := by omega
    simp only [Fin.val_last, hm0, dite_true, lt_self_iff_false,
      dite_false] at hxf_terminal
    have hprev : finitePathPrev (Fin.last m) hm0 = ⟨m - 1, by omega⟩ := by
      apply Fin.ext
      simp [finitePathPrev]
    rw [hprev, hunit] at hxf_terminal
    simp only [An, cn, sn, xfn,
      finitePathNatLift_of_lt (i := m) (G.gapA p e) (by omega),
      finitePathNatLift_of_lt (i := m - 1) (G.gapS weight) (by omega),
      finitePathNatLift_of_lt (i := m - 1) xf (by omega),
      finitePathNatLift_of_lt (i := m) (G.gapC weight q e rho) (by omega),
      finitePathNatLift_of_lt (i := m) xf (by omega)]
    have hlast : (Fin.last m : Fin (m + 1)) = ⟨m, by omega⟩ := by
      apply Fin.ext
      simp
    rw [hlast] at hxf_terminal
    linear_combination hxf_terminal
  dsimp only [SourceGapEmbedding.properWrapState, An, cn, sn, xfn, eff]
  exact two_reaction_right_diagonal_eq heffPos.1 (hAn m) (hcn (m - 1))
    (hcn m) (hsn (m - 1)) hforward₀ hforward₁

/-- The same exact right-core identity for a two-coordinate literal gap.
Here the first coordinate is also the penultimate coordinate, so its forcing
is `c₀` rather than zero; keeping this case separate avoids an artificial
`1 < m` premise in the cyclic Schur argument. -/
theorem SourceGapEmbedding.restricted_two_coordinate_right_diagonal_core_eq
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (hm : m = 1)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (xf : Fin (m + 1) → ℝ) {scale k h g : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : G.gapS weight (Fin.last m) = 1)
    (hxf0 :
      ∑ j, G.restrictedCurrentMatrix weight p q e rho 0 j * xf j =
        G.gapC weight q e rho 0)
    (hxf1 :
      ∑ j, G.restrictedCurrentMatrix weight p q e rho (Fin.last m) j * xf j =
        -(G.gapA p e (Fin.last m) +
          G.gapC weight q e rho (Fin.last m))) :
    let eff := G.properWrapState weight p q e rho scale k
    let Aeff := wrapCondensedA eff.A (finitePathNatLift (G.gapA p e) m)
      (finitePathNatLift (G.gapC weight q e rho) (m - 1))
      (finitePathNatLift (G.gapS weight) (m - 1))
    let heff := wrapCondensedH eff.A
      (finitePathNatLift (G.gapC weight q e rho) (m - 1))
      (finitePathNatLift (G.gapS weight) (m - 1)) h
    let d := 1 + Aeff + finitePathNatLift (G.gapC weight q e rho) m
    1 + g + h -
        (h * finitePathNatLift (G.gapS weight) (m - 1) *
            finitePathNatLift xf (m - 1) -
          (g + h) * finitePathNatLift xf m) =
      (d + g + heff) / d := by
  subst m
  have h0 := hxf0
  have h1 := hxf1
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix,
    finiteSourcePathMatrix_mul_apply] at h0 h1
  rw [hunit] at h1
  have hrow0 :
      wrapPrefixPivot (G.gapA p e 0) (G.gapC weight q e rho 0)
          (G.gapS weight 0) * xf 0 -
        G.gapC weight q e rho 0 * xf 1 =
          G.gapC weight q e rho 0 := by
    simpa [wrapPrefixPivot, finitePathNext, sub_eq_add_neg] using h0
  have hrow1 :
      -(G.gapA p e 1 * G.gapS weight 0) * xf 0 +
          (1 + G.gapA p e 1 + G.gapC weight q e rho 1) * xf 1 =
        -(G.gapA p e 1 + G.gapC weight q e rho 1) := by
    simp [finitePathPrev] at h1
    linear_combination h1
  simpa [SourceGapEmbedding.properWrapState, natWrapPrefixState,
    finitePathNatLift_of_lt, SourceGapEmbedding.gapA, SourceGapEmbedding.gapC] using
      (two_reaction_right_diagonal_eq
        (div_pos (hp _) (he _)) (div_pos (hp _) (he _))
        (mul_pos (hq _) (div_pos
          (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _)))
        (mul_pos (hq _) (div_pos
          (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _)))
        (G.gapS_pos hw 0) hrow0 hrow1)

end TypeIIL

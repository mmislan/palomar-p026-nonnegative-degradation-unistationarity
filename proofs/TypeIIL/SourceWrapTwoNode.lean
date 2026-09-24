import proofs.TypeIIL.SourceWrapCondensation

namespace TypeIIL

/-- Exact forward Schur entry for a two-reaction source gap.  The direct
two-by-two inverse formula agrees with the staged prefix condensation. -/
theorem two_reaction_forward_condensation_eq
    {A₀ A₁ c₀ c₁ s₀ k : ℝ}
    (hpivot : wrapPrefixPivot A₀ c₀ s₀ ≠ 0) :
    k * c₀ /
        (wrapPrefixPivot A₀ c₀ s₀ * (1 + A₁ + c₁) -
          A₁ * s₀ * c₀) =
      wrapCondensedK A₀ c₀ s₀ k /
        (1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁) := by
  unfold wrapCondensedA wrapCondensedK
  field_simp
  unfold wrapPrefixPivot
  ring

/-- Exact exceptional predecessor Schur entry for a two-reaction source
gap.  Crucially, `c₀` is the eliminated edge coefficient while `c₁` is the
independent terminal diagonal coefficient. -/
theorem two_reaction_wrap_condensation_eq
    {A₀ A₁ c₀ c₁ s₀ scale h g : ℝ}
    (hone : 1 + A₀ ≠ 0)
    (hpivot : wrapPrefixPivot A₀ c₀ s₀ ≠ 0) :
    A₀ * scale * s₀ * (h * (1 + c₁) - g * A₁) /
        (wrapPrefixPivot A₀ c₀ s₀ * (1 + A₁ + c₁) -
          A₁ * s₀ * c₀) =
      wrapCondensedScale A₀ s₀ scale *
        (wrapCondensedH A₀ c₀ s₀ h * (1 + c₁) -
          g * wrapCondensedA A₀ A₁ c₀ s₀) /
        (1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁) := by
  unfold wrapCondensedA wrapCondensedScale wrapCondensedH
  field_simp
  unfold wrapPrefixPivot
  ring

/-- Under positive source coefficients the denominators required by both
two-reaction identities are automatically positive. -/
theorem two_reaction_condensation_denominators_pos
    {A₀ A₁ c₀ c₁ s₀ : ℝ}
    (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hs₀ : 0 < s₀) :
    0 < wrapPrefixPivot A₀ c₀ s₀ ∧
      0 < 1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁ := by
  have hpivot := wrapPrefixPivot_pos (le_of_lt hA₀) (le_of_lt hc₀)
    (le_of_lt hs₀)
  constructor
  · exact hpivot
  · have hAeff : 0 < wrapCondensedA A₀ A₁ c₀ s₀ := by
      unfold wrapCondensedA
      exact div_pos (mul_pos hA₁ (by linarith)) hpivot
    linarith

/-- Solution-level forward response of the literal two-reaction block.  This
avoids choosing a matrix-inverse representation and is the form needed by
the arbitrary-path Gaussian induction. -/
theorem two_reaction_forward_response_eq
    {A₀ A₁ c₀ c₁ s₀ k x₀ x₁ : ℝ}
    (hdet :
      wrapPrefixPivot A₀ c₀ s₀ * (1 + A₁ + c₁) -
        A₁ * s₀ * c₀ ≠ 0)
    (hrow₀ : wrapPrefixPivot A₀ c₀ s₀ * x₀ - c₀ * x₁ = c₀)
    (hrow₁ : -(A₁ * s₀) * x₀ + (1 + A₁ + c₁) * x₁ =
      -(A₁ + c₁)) :
    k * x₀ = k * c₀ /
      (wrapPrefixPivot A₀ c₀ s₀ * (1 + A₁ + c₁) -
        A₁ * s₀ * c₀) := by
  have hx :
      (wrapPrefixPivot A₀ c₀ s₀ * (1 + A₁ + c₁) -
          A₁ * s₀ * c₀) * x₀ = c₀ := by
    linear_combination (1 + A₁ + c₁) * hrow₀ + c₀ * hrow₁
  rw [eq_div_iff hdet]
  linear_combination k * hx

/-- Solution-level exceptional predecessor response of the same literal
two-reaction block. -/
theorem two_reaction_wrap_response_eq
    {A₀ A₁ c₀ c₁ s₀ scale h g y₀ y₁ : ℝ}
    (hdet :
      wrapPrefixPivot A₀ c₀ s₀ * (1 + A₁ + c₁) -
        A₁ * s₀ * c₀ ≠ 0)
    (hrow₀ : wrapPrefixPivot A₀ c₀ s₀ * y₀ - c₀ * y₁ =
      -(A₀ * scale))
    (hrow₁ : -(A₁ * s₀) * y₀ + (1 + A₁ + c₁) * y₁ = 0) :
    -(h * s₀ * y₀ - (g + h) * y₁) =
      A₀ * scale * s₀ * (h * (1 + c₁) - g * A₁) /
        (wrapPrefixPivot A₀ c₀ s₀ * (1 + A₁ + c₁) -
          A₁ * s₀ * c₀) := by
  let det := wrapPrefixPivot A₀ c₀ s₀ * (1 + A₁ + c₁) -
    A₁ * s₀ * c₀
  have hy₀ : det * y₀ = -(A₀ * scale * (1 + A₁ + c₁)) := by
    dsimp [det]
    linear_combination (1 + A₁ + c₁) * hrow₀ + c₀ * hrow₁
  have hy₁ : det * y₁ = -(A₀ * scale * A₁ * s₀) := by
    dsimp [det]
    linear_combination (A₁ * s₀) * hrow₀ +
      wrapPrefixPivot A₀ c₀ s₀ * hrow₁
  rw [eq_div_iff hdet]
  dsimp [det] at hy₀ hy₁ ⊢
  linear_combination -h * s₀ * hy₀ + (g + h) * hy₁

/-- Exact grouped left-fork diagonal identity for the final two-node block.
After the mixed left response is combined with its direct boundary product,
the compiled endpoint core remains, plus the strictly favorable discarded
budget `k * scale / (1 + A₀)`. -/
theorem two_reaction_left_diagonal_budget_eq
    {A₀ A₁ c₀ c₁ s₀ scale k y₀ y₁ : ℝ}
    (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hs₀ : 0 < s₀)
    (hrow₀ : wrapPrefixPivot A₀ c₀ s₀ * y₀ - c₀ * y₁ =
      -(A₀ * scale))
    (hrow₁ : -(A₁ * s₀) * y₀ + (1 + A₁ + c₁) * y₁ = 0) :
    1 + k * scale + k * y₀ =
      let Aeff := wrapCondensedA A₀ A₁ c₀ s₀
      let seff := wrapCondensedScale A₀ s₀ scale
      let keff := wrapCondensedK A₀ c₀ s₀ k
      let d := 1 + Aeff + c₁
      (d + keff * seff * (1 + c₁)) / d + k * scale / (1 + A₀) := by
  let det := wrapPrefixPivot A₀ c₀ s₀ * (1 + A₁ + c₁) -
    A₁ * s₀ * c₀
  have hdenoms := two_reaction_condensation_denominators_pos
    hA₀ hA₁ hc₀ hc₁ hs₀
  have hpivot : wrapPrefixPivot A₀ c₀ s₀ ≠ 0 := ne_of_gt hdenoms.1
  have hone : 1 + A₀ ≠ 0 := by linarith
  have hfactor :
      det = wrapPrefixPivot A₀ c₀ s₀ *
        (1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁) := by
    dsimp [det]
    unfold wrapCondensedA
    field_simp [hpivot]
    unfold wrapPrefixPivot
    ring
  have hdetpos : 0 < det := by
    rw [hfactor]
    exact mul_pos hdenoms.1 hdenoms.2
  have hdet : det ≠ 0 := ne_of_gt hdetpos
  have hy : y₀ = -(A₀ * scale * (1 + A₁ + c₁)) / det := by
    apply (eq_div_iff hdet).2
    dsimp [det]
    linear_combination (1 + A₁ + c₁) * hrow₀ + c₀ * hrow₁
  have hdenEq :
      1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁ =
        det / wrapPrefixPivot A₀ c₀ s₀ := by
    apply (eq_div_iff hpivot).2
    rw [hfactor]
    ring
  have hprodEq :
      wrapCondensedK A₀ c₀ s₀ k *
          wrapCondensedScale A₀ s₀ scale =
        k * c₀ * scale * s₀ * A₀ /
          (wrapPrefixPivot A₀ c₀ s₀ * (1 + A₀)) := by
    unfold wrapCondensedK wrapCondensedScale
    field_simp [hpivot, hone]
  dsimp only
  rw [hy, hdenEq, hprodEq]
  field_simp [hdet, hpivot, hone]
  unfold det wrapPrefixPivot
  ring

/-- Exact grouped right-fork diagonal identity for the final two-node block.
The shifted terminal trace satisfies `det * (x₁ + 1) = pivot`; together with
`det * x₀ = c₀`, the cancellation `pivot - s₀*c₀ = 1 + A₀` is precisely the
condensed back coefficient. -/
theorem two_reaction_right_diagonal_eq
    {A₀ A₁ c₀ c₁ s₀ h g x₀ x₁ : ℝ}
    (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hs₀ : 0 < s₀)
    (hrow₀ : wrapPrefixPivot A₀ c₀ s₀ * x₀ - c₀ * x₁ = c₀)
    (hrow₁ : -(A₁ * s₀) * x₀ + (1 + A₁ + c₁) * x₁ =
      -(A₁ + c₁)) :
    1 + g + h - (h * s₀ * x₀ - (g + h) * x₁) =
      let Aeff := wrapCondensedA A₀ A₁ c₀ s₀
      let heff := wrapCondensedH A₀ c₀ s₀ h
      let d := 1 + Aeff + c₁
      (d + g + heff) / d := by
  let pivot := wrapPrefixPivot A₀ c₀ s₀
  let det := pivot * (1 + A₁ + c₁) - A₁ * s₀ * c₀
  have hdenoms := two_reaction_condensation_denominators_pos
    hA₀ hA₁ hc₀ hc₁ hs₀
  have hpivot : 0 < pivot := by simpa [pivot] using hdenoms.1
  have hpivot0 : pivot ≠ 0 := ne_of_gt hpivot
  have hpivotRaw : wrapPrefixPivot A₀ c₀ s₀ ≠ 0 := ne_of_gt hdenoms.1
  have hd : 0 < 1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁ := hdenoms.2
  have hd0 : 1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁ ≠ 0 := ne_of_gt hd
  have hfactor : det =
      pivot * (1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁) := by
    dsimp [det, pivot]
    unfold wrapCondensedA
    field_simp [hpivotRaw]
    unfold wrapPrefixPivot
    ring
  have hdet : det ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero hpivot0 hd0
  have hx₀ : det * x₀ = c₀ := by
    dsimp [det, pivot]
    linear_combination (1 + A₁ + c₁) * hrow₀ + c₀ * hrow₁
  have hx₁ : det * (x₁ + 1) = pivot := by
    have hraw : det * x₁ =
        -(pivot * (A₁ + c₁)) + A₁ * s₀ * c₀ := by
      dsimp [det, pivot]
      linear_combination (A₁ * s₀) * hrow₀ +
        wrapPrefixPivot A₀ c₀ s₀ * hrow₁
    dsimp [det]
    nlinarith [hraw]
  have hlhs :
      1 + g + h - (h * s₀ * x₀ - (g + h) * x₁) =
        1 + ((g + h) * (x₁ + 1) - h * s₀ * x₀) := by ring
  rw [hlhs]
  dsimp only
  unfold wrapCondensedH
  change 1 + ((g + h) * (x₁ + 1) - h * s₀ * x₀) =
    ((1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁) + g +
      h * (1 + A₀) / pivot) /
        (1 + wrapCondensedA A₀ A₁ c₀ s₀ + c₁)
  apply (eq_div_iff hd0).2
  apply (mul_left_cancel₀ hpivot0)
  rw [mul_assoc]
  field_simp [hpivot0]
  rw [hfactor] at hx₀ hx₁
  dsimp [det, pivot] at hx₀ hx₁ ⊢
  unfold wrapPrefixPivot at hx₀ hx₁ ⊢
  linear_combination (g + h) * hx₁ - h * s₀ * hx₀

end TypeIIL

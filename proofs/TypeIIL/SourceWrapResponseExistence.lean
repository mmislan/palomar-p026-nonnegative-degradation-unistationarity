import proofs.TypeIIL.SourceGapResponseExistence
import proofs.TypeIIL.SourceWrapLiteralResponse

namespace TypeIIL

open scoped BigOperators

/-- Mixed forcing created by the literal right-fork column of a long source
gap: positive at the penultimate coordinate and negative at the terminal. -/
def sourceWrapForwardForcing {m : ℕ}
    (A c : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ := fun i =>
  if i.val = m - 1 then c i
  else if i.val = m then -(A i + c i)
  else 0

/-- Forcing created by the literal left-fork column. -/
def sourceWrapLeftForcing {m : ℕ}
    (A : Fin (m + 1) → ℝ) (scale : ℝ) : Fin (m + 1) → ℝ := fun i =>
  if i.val = 0 then -(A i * scale) else 0

/-- A literal positive long source gap admits both Schur responses, and their
actual mixed boundary equations force the strict raw two-edge margin.  Thus
`xf`, `yw`, `Fprev`, and `W` are constructed here rather than exposed as
hypotheses. -/
theorem SourceGapEmbedding.exists_responses_and_raw_two_edge_margin
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (hm : 1 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    {scale k h g X Bprev : ℝ}
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
          precedingCorrection) :
    ∃ xf yw : Fin (m + 1) → ℝ,
      (∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
        sourceWrapForwardForcing (G.gapA p e)
          (G.gapC weight q e rho) i) ∧
      (∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
        sourceWrapLeftForcing (G.gapA p e) scale i) ∧
      let eff := G.properWrapState weight p q e rho scale k
      let Fprev := eff.k * finitePathNatLift xf (m - 1)
      let W := -(h * finitePathNatLift (G.gapS weight) (m - 1) *
          finitePathNatLift yw (m - 1) -
        (g + h) * finitePathNatLift yw m)
      W * Fprev < X * Bprev := by
  obtain ⟨xf, hxf⟩ := G.restricted_response_exists weight p q e rho
    (fun r => le_of_lt (hp r)) (fun r => le_of_lt (hq r)) he hrho hw
    (sourceWrapForwardForcing (G.gapA p e) (G.gapC weight q e rho))
  obtain ⟨yw, hyw⟩ := G.restricted_response_exists weight p q e rho
    (fun r => le_of_lt (hp r)) (fun r => le_of_lt (hq r)) he hrho hw
    (sourceWrapLeftForcing (G.gapA p e) scale)
  refine ⟨xf, yw, hxf, hyw, ?_⟩
  apply G.restricted_response_raw_two_edge_margin hm weight p q e rho xf yw
    hp hq he hrho hw hscale hk hunit hh hg hfollowing hpreceding hX hBprev
  · have h0m1 : 0 ≠ m - 1 := by omega
    have h0m : 0 ≠ m := by omega
    simpa [sourceWrapForwardForcing, h0m1, h0m] using hxf 0
  · intro i hi him
    have hi1 : i.val ≠ m - 1 := by omega
    have him' : i.val ≠ m := by omega
    simpa [sourceWrapForwardForcing, hi1, him'] using hxf i
  · simpa [sourceWrapForwardForcing] using hxf ⟨m - 1, by omega⟩
  · have hmm1 : m ≠ m - 1 := by omega
    simpa [sourceWrapForwardForcing, hmm1] using hxf (Fin.last m)
  · simpa [sourceWrapLeftForcing] using hyw 0
  · intro i hi him
    have hi0 : i.val ≠ 0 := by omega
    simpa [sourceWrapLeftForcing, hi0] using hyw i
  · have hm10 : m - 1 ≠ 0 := by omega
    simpa [sourceWrapLeftForcing, hm10] using hyw ⟨m - 1, by omega⟩
  · have hm0 : m ≠ 0 := by omega
    simpa [sourceWrapLeftForcing, hm0] using hyw (Fin.last m)
  · rfl
  · rfl

/-- The first weak-gap case (`m = 1`) is the same two-port calculation with
an empty proper prefix.  Keeping it beside the long-gap theorem makes the
source adapter exhaustive without pretending that `1 < m`. -/
theorem SourceGapEmbedding.exists_two_coordinate_responses_and_raw_margin
    {n : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back 1)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    {scale k h g X Bprev : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 < scale) (hk : 0 < k)
    (hunit : G.gapS weight (Fin.last 1) = 1)
    (hh : 0 < h) (hg : 0 ≤ g)
    {followingBudget precedingCorrection : ℝ}
    (hfollowing : 0 ≤ followingBudget)
    (hpreceding : precedingCorrection ≤ 0)
    (hX :
      let eff := G.properWrapState weight p q e rho scale k
      let Aeff := wrapCondensedA eff.A (finitePathNatLift (G.gapA p e) 1)
        (finitePathNatLift (G.gapC weight q e rho) 0)
        (finitePathNatLift (G.gapS weight) 0)
      let heffR := wrapCondensedH eff.A
        (finitePathNatLift (G.gapC weight q e rho) 0)
        (finitePathNatLift (G.gapS weight) 0) h
      let d := 1 + Aeff + finitePathNatLift (G.gapC weight q e rho) 1
      X = (d + g + heffR) / d + followingBudget)
    (hBprev :
      let eff := G.properWrapState weight p q e rho scale k
      let Aeff := wrapCondensedA eff.A (finitePathNatLift (G.gapA p e) 1)
        (finitePathNatLift (G.gapC weight q e rho) 0)
        (finitePathNatLift (G.gapS weight) 0)
      let seff := wrapCondensedScale eff.A
        (finitePathNatLift (G.gapS weight) 0) eff.scale
      let keff := wrapCondensedK eff.A
        (finitePathNatLift (G.gapC weight q e rho) 0)
        (finitePathNatLift (G.gapS weight) 0) eff.k
      let d := 1 + Aeff + finitePathNatLift (G.gapC weight q e rho) 1
      Bprev = (d + keff * seff *
        (1 + finitePathNatLift (G.gapC weight q e rho) 1)) / d -
          precedingCorrection) :
    ∃ xf yw : Fin 2 → ℝ,
      (∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
        sourceWrapForwardForcing (G.gapA p e)
          (G.gapC weight q e rho) i) ∧
      (∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
        sourceWrapLeftForcing (G.gapA p e) scale i) ∧
      let eff := G.properWrapState weight p q e rho scale k
      let Fprev := eff.k * finitePathNatLift xf 0
      let W := -(h * finitePathNatLift (G.gapS weight) 0 *
          finitePathNatLift yw 0 - (g + h) * finitePathNatLift yw 1)
      W * Fprev < X * Bprev := by
  obtain ⟨xf, hxf⟩ := G.restricted_response_exists weight p q e rho
    (fun r => le_of_lt (hp r)) (fun r => le_of_lt (hq r)) he hrho hw
    (sourceWrapForwardForcing (G.gapA p e) (G.gapC weight q e rho))
  obtain ⟨yw, hyw⟩ := G.restricted_response_exists weight p q e rho
    (fun r => le_of_lt (hp r)) (fun r => le_of_lt (hq r)) he hrho hw
    (sourceWrapLeftForcing (G.gapA p e) scale)
  refine ⟨xf, yw, hxf, hyw, ?_⟩
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hxf hyw
  apply finiteSourcePath_two_node_response_raw_two_edge_margin
    (G.gapA p e) (G.gapC weight q e rho) (G.gapS weight) xf yw
      (scale := scale) (k := k) (h := h) (g := g)
      (followingBudget := followingBudget)
      (precedingCorrection := precedingCorrection)
  · exact fun i => div_pos (hp _) (he _)
  · intro i
    unfold SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  · exact G.gapS_pos hw
  · simpa using hunit
  · exact hscale
  · exact hk
  · exact hh
  · exact hg
  · exact hfollowing
  · exact hpreceding
  · simpa [SourceGapEmbedding.properWrapState] using hX
  · simpa [SourceGapEmbedding.properWrapState] using hBprev
  · simpa [sourceWrapForwardForcing] using hxf 0
  · simpa [sourceWrapForwardForcing] using hxf 1
  · simpa [sourceWrapLeftForcing] using hyw 0
  · simpa [sourceWrapLeftForcing] using hyw 1
  · rfl
  · rfl

end TypeIIL

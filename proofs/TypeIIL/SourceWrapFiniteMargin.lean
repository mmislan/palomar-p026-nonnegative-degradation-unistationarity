import proofs.TypeIIL.SourceWrapFiniteInduction

namespace TypeIIL

/-- The finite-path state used by the literal equation induction feeds
directly into the arbitrary-prefix coupled-margin theorem.  This is the
inverse-free Schur-to-fold docking: no independent matrix inverse or
coefficientwise wrap estimate is assumed. -/
theorem finiteSourcePath_raw_two_edge_margin
    {m : ℕ} (r : ℕ) (A c s : Fin (m + 1) → ℝ) {scale k : ℝ}
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i) (hs : ∀ i, 0 < s i)
    (hscale : 0 < scale) (hk : 0 < k)
    {nextA edgeC edgeS terminalC h g X Bprev Fprev W : ℝ}
    (hnextA : 0 < nextA) (hedgeC : 0 < edgeC)
    (hedgeS : 0 < edgeS) (hterminalC : 0 < terminalC)
    (hh : 0 < h) (hg : 0 ≤ g)
    (hX :
      let eff := natWrapPrefixState (finitePathNatLift A)
        (finitePathNatLift c) (finitePathNatLift s) scale k r
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let heff := wrapCondensedH eff.A edgeC edgeS h
      let d := 1 + Aeff + terminalC
      (d + g + heff) / d ≤ X)
    (hBprev :
      let eff := natWrapPrefixState (finitePathNatLift A)
        (finitePathNatLift c) (finitePathNatLift s) scale k r
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let seff := wrapCondensedScale eff.A edgeS eff.scale
      let keff := wrapCondensedK eff.A edgeC edgeS eff.k
      let d := 1 + Aeff + terminalC
      (d + keff * seff * (1 + terminalC)) / d ≤ Bprev)
    (hFprev :
      let eff := natWrapPrefixState (finitePathNatLift A)
        (finitePathNatLift c) (finitePathNatLift s) scale k r
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let keff := wrapCondensedK eff.A edgeC edgeS eff.k
      let d := 1 + Aeff + terminalC
      Fprev = keff / d)
    (hW :
      let eff := natWrapPrefixState (finitePathNatLift A)
        (finitePathNatLift c) (finitePathNatLift s) scale k r
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let seff := wrapCondensedScale eff.A edgeS eff.scale
      let heff := wrapCondensedH eff.A edgeC edgeS h
      let d := 1 + Aeff + terminalC
      W = seff * (heff * (1 + terminalC) - g * Aeff) / d) :
    W * Fprev < X * Bprev := by
  let An := finitePathNatLift A
  let cn := finitePathNatLift c
  let sn := finitePathNatLift s
  let st := natWrapPrefixState An cn sn scale k 0
  let steps := natWrapPrefixSteps An cn sn r
  have hAn : ∀ i, 0 < An i := fun i => hA _
  have hcn : ∀ i, 0 < cn i := fun i => hc _
  have hsn : ∀ i, 0 < sn i := fun i => hs _
  have hst : st.StrictlyPositive := by
    exact natWrapPrefixState_pos An cn sn hAn hcn hsn hscale hk 0
  have hsteps : ∀ step ∈ steps,
      0 < step.1 ∧ 0 < step.2.1 ∧ 0 < step.2.2 := by
    intro step hstep
    simp only [steps, natWrapPrefixSteps, List.mem_map,
      List.mem_range] at hstep
    obtain ⟨i, hi, rfl⟩ := hstep
    exact ⟨hAn (i + 1), hcn i, hsn i⟩
  have heq : wrapPrefixFold st steps =
      natWrapPrefixState An cn sn scale k r := by
    exact (natWrapPrefixState_eq_fold An cn sn scale k r).symm
  apply wrapPrefixFold_raw_two_edge_margin steps st hst hsteps
      hnextA hedgeC hedgeS hterminalC hh hg
  · simpa only [An, cn, sn, heq] using hX
  · simpa only [An, cn, sn, heq] using hBprev
  · simpa only [An, cn, sn, heq] using hFprev
  · simpa only [An, cn, sn, heq] using hW

/-- The effective prefix state of a literal source gap, with its final edge
reserved for the terminal two-node condensation. -/
noncomputable def SourceGapEmbedding.properWrapState
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (scale k : ℝ) : WrapPrefixState :=
  natWrapPrefixState (finitePathNatLift (G.gapA p e))
    (finitePathNatLift (G.gapC weight q e rho))
    (finitePathNatLift (G.gapS weight)) scale k (m - 1)

/-- Literal source form of the grouped left-fork diagonal estimate. -/
theorem SourceGapEmbedding.restricted_left_diagonal_core_le
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (yw : Fin (m + 1) → ℝ) {scale k : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 < scale) (hk : 0 < k)
    (hunit : G.gapS weight (Fin.last m) = 1)
    (hyw : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
        if i.val = 0 then -(G.gapA p e i * scale) else 0) :
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
    (d + keff * seff *
      (1 + finitePathNatLift (G.gapC weight q e rho) m)) / d ≤
        1 + k * scale + k * yw 0 := by
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hyw
  apply finiteSourcePath_left_diagonal_core_le hm
    (G.gapA p e) (G.gapC weight q e rho) (G.gapS weight) yw
  · exact fun i => div_pos (hp _) (he _)
  · intro i
    unfold SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  · exact G.gapS_pos hw
  · exact hscale
  · exact hk
  · exact hunit
  · simpa using hyw 0
  · intro i hi him
    have hi0 : i.val ≠ 0 := by omega
    simpa [hi0] using hyw i
  · have hm0 : m ≠ 0 := by omega
    simpa [hm0] using hyw (Fin.last m)

/-- Literal source-coefficient form of the coupled wrap margin. -/
theorem SourceGapEmbedding.restricted_raw_two_edge_margin
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    {scale k nextA edgeC edgeS terminalC h g X Bprev Fprev W : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 < scale) (hk : 0 < k)
    (hnextA : 0 < nextA) (hedgeC : 0 < edgeC)
    (hedgeS : 0 < edgeS) (hterminalC : 0 < terminalC)
    (hh : 0 < h) (hg : 0 ≤ g)
    (hX :
      let eff := G.properWrapState weight p q e rho scale k
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let heff := wrapCondensedH eff.A edgeC edgeS h
      let d := 1 + Aeff + terminalC
      (d + g + heff) / d ≤ X)
    (hBprev :
      let eff := G.properWrapState weight p q e rho scale k
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let seff := wrapCondensedScale eff.A edgeS eff.scale
      let keff := wrapCondensedK eff.A edgeC edgeS eff.k
      let d := 1 + Aeff + terminalC
      (d + keff * seff * (1 + terminalC)) / d ≤ Bprev)
    (hFprev :
      let eff := G.properWrapState weight p q e rho scale k
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let keff := wrapCondensedK eff.A edgeC edgeS eff.k
      let d := 1 + Aeff + terminalC
      Fprev = keff / d)
    (hW :
      let eff := G.properWrapState weight p q e rho scale k
      let Aeff := wrapCondensedA eff.A nextA edgeC edgeS
      let seff := wrapCondensedScale eff.A edgeS eff.scale
      let heff := wrapCondensedH eff.A edgeC edgeS h
      let d := 1 + Aeff + terminalC
      W = seff * (heff * (1 + terminalC) - g * Aeff) / d) :
    W * Fprev < X * Bprev := by
  apply finiteSourcePath_raw_two_edge_margin (m - 1)
    (G.gapA p e) (G.gapC weight q e rho) (G.gapS weight)
  · intro i
    exact div_pos (hp _) (he _)
  · intro i
    unfold SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  · exact G.gapS_pos hw
  · exact hscale
  · exact hk
  · simpa only [SourceGapEmbedding.properWrapState] using hnextA
  · exact hedgeC
  · exact hedgeS
  · exact hterminalC
  · exact hh
  · exact hg
  · simpa only [SourceGapEmbedding.properWrapState] using hX
  · simpa only [SourceGapEmbedding.properWrapState] using hBprev
  · simpa only [SourceGapEmbedding.properWrapState] using hFprev
  · simpa only [SourceGapEmbedding.properWrapState] using hW

end TypeIIL

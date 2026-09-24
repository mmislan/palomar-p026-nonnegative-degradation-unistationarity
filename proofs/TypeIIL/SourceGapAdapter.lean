import proofs.TypeIIL.SourceCurrentMatrix
import proofs.TypeIIL.SourceFinitePath

namespace TypeIIL

/-- Exact indexing data for one nonempty paper gap.  This is not a normalized
network: `idx` embeds the literal consecutive nonfork reactions/species of the
raw source cycle.  The predecessor equivalence is the finite-interval ledger
that the paper ordering must discharge. -/
structure SourceGapEmbedding {n : ℕ}
    (next : Fin n ≃ Fin n) (back : Fin n → Option (Fin n)) (m : ℕ) where
  idx : Fin (m + 1) ↪ Fin n
  nonfork : ∀ i, back (idx i) = none
  successor_support : ∀ i j,
    next (idx i) = idx j ↔
      ∃ h : i.val < m, j = finitePathNext i h
  predecessor_support : ∀ i j,
    next (idx j) = idx i ↔
      ∃ h : 0 < i.val, j = finitePathPrev i h
  no_two_cycle : ∀ x, x ≠ next (next x)

namespace SourceGapEmbedding

variable {n m : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

theorem idx_step (G : SourceGapEmbedding next back m)
    (i : Fin (m + 1)) (hi : i.val < m) :
    next (G.idx i) = G.idx (finitePathNext i hi) := by
  exact (G.successor_support i (finitePathNext i hi)).mpr ⟨hi, rfl⟩

theorem idx_ne_next (G : SourceGapEmbedding next back m)
    (i : Fin (m + 1)) : G.idx i ≠ next (G.idx i) := by
  intro h
  have hs := (G.predecessor_support i i).mp h.symm
  rcases hs with ⟨hi, heq⟩
  have hval := congrArg Fin.val heq
  dsimp [finitePathPrev] at hval
  omega

theorem next_next_ne (G : SourceGapEmbedding next back m)
    (i : Fin (m + 1)) (hi : i.val < m) :
    G.idx i ≠ next (next (G.idx i)) := by
  intro h
  rw [G.idx_step i hi] at h
  have hs := (G.predecessor_support i (finitePathNext i hi)).mp h.symm
  rcases hs with ⟨hipos, heq⟩
  have hval := congrArg Fin.val heq
  dsimp [finitePathNext, finitePathPrev] at hval
  omega

theorem next_ne_next_next (G : SourceGapEmbedding next back m)
    (i : Fin (m + 1)) :
    next (G.idx i) ≠ next (next (G.idx i)) := by
  exact fun h => G.idx_ne_next i (next.injective h)

theorem idx_prev_step (G : SourceGapEmbedding next back m)
    (i : Fin (m + 1)) (hi : 0 < i.val) :
    next (G.idx (finitePathPrev i hi)) = G.idx i := by
  exact (G.predecessor_support i (finitePathPrev i hi)).mpr ⟨hi, rfl⟩

theorem idx_prev_ne (G : SourceGapEmbedding next back m)
    (i : Fin (m + 1)) (hi : 0 < i.val) :
    G.idx (finitePathPrev i hi) ≠ G.idx i := by
  apply G.idx.injective.ne
  intro h
  have hval := congrArg Fin.val h
  dsimp [finitePathPrev] at hval
  omega

theorem idx_prev_ne_next (G : SourceGapEmbedding next back m)
    (i : Fin (m + 1)) (hi : 0 < i.val) :
    G.idx (finitePathPrev i hi) ≠ next (G.idx i) := by
  intro h
  apply G.no_two_cycle (G.idx i)
  calc
    G.idx i = next (G.idx (finitePathPrev i hi)) :=
      (G.idx_prev_step i hi).symm
    _ = next (next (G.idx i)) := congrArg next h

noncomputable def gapA (G : SourceGapEmbedding next back m)
    (p e : Fin n → ℝ) : Fin (m + 1) → ℝ :=
  fun i => p (G.idx i) / e (G.idx i)

noncomputable def gapC (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) (q e rho : Fin n → ℝ) :
    Fin (m + 1) → ℝ :=
  fun i => q (G.idx i) *
    (TypeII3.secantPoly (rho (next (G.idx i))) 1 (weight (G.idx i)) /
      e (next (G.idx i)))

def gapS (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) : Fin (m + 1) → ℝ :=
  fun i => weight (G.idx i)

noncomputable def restrictedCurrentMatrix
    (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix
      (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e (G.idx i) (G.idx j)

/-- The literal current matrix restricted to one paper gap is exactly the
finite weighted path block. -/
theorem restrictedCurrentMatrix_eq_finiteSourcePathMatrix
    (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ) :
    restrictedCurrentMatrix G weight p q e rho =
      finiteSourcePathMatrix (G.gapA p e) (G.gapC weight q e rho)
        (G.gapS weight) := by
  funext i j
  unfold restrictedCurrentMatrix
  by_cases hij : j = i
  · subst j
    rw [sourceOrderedCurrentMatrix_nonfork_diagonal next weight back
      (G.nonfork i) (G.idx_ne_next i)]
    have hprev : ∀ h : 0 < i.val, i ≠ finitePathPrev i h := by
      intro h heq
      have hval := congrArg Fin.val heq
      dsimp [finitePathPrev] at hval
      omega
    have hnext : ∀ h : i.val < m, i ≠ finitePathNext i h := by
      intro h heq
      have hval := congrArg Fin.val heq
      dsimp [finitePathNext] at hval
      omega
    simp [finiteSourcePathMatrix, gapA, gapC, gapS, hprev, hnext]
  · by_cases hpred : ∃ h : 0 < i.val, j = finitePathPrev i h
    · rcases hpred with ⟨hi, rfl⟩
      rw [sourceOrderedCurrentMatrix_nonfork_predecessor next weight back
        (G.nonfork i) (G.nonfork (finitePathPrev i hi))
        (G.idx_prev_step i hi) (G.idx_prev_ne i hi)
        (G.idx_prev_ne_next i hi) (G.idx_ne_next i)]
      unfold finiteSourcePathMatrix
      rw [ite_eq_right hij, dite_eq_left hi, ite_eq_left rfl]
      by_cases hn : i.val < m
      · rw [dite_eq_left hn, ite_eq_right]
        · simp [gapA, gapS]
        · intro heq
          have hval := congrArg Fin.val heq
          dsimp [finitePathPrev, finitePathNext] at hval
          omega
      · rw [dite_eq_right hn]
        simp [gapA, gapS]
    · by_cases hsucc : ∃ h : i.val < m, j = finitePathNext i h
      · rcases hsucc with ⟨hi, rfl⟩
        have hbackNext : back (next (G.idx i)) = none := by
          rw [G.idx_step i hi]
          exact G.nonfork (finitePathNext i hi)
        rw [← G.idx_step i hi]
        rw [sourceOrderedCurrentMatrix_nonfork_successor next weight back
          (G.nonfork i) (G.idx_ne_next i) (G.no_two_cycle (G.idx i))
          hbackNext (G.next_ne_next_next i)]
        have hprevTerm :
            (if h : 0 < i.val then
              if finitePathNext i hi = finitePathPrev i h then
                -(G.gapA p e i * G.gapS weight (finitePathPrev i h))
              else 0
            else 0) = 0 := by
          by_cases hp : 0 < i.val
          · rw [dite_eq_left hp, ite_eq_right]
            intro heq
            have hval := congrArg Fin.val heq
            dsimp [finitePathPrev, finitePathNext] at hval
            omega
          · rw [dite_eq_right hp]
        have hnextTerm :
            (if h : i.val < m then
              if finitePathNext i hi = finitePathNext i h then
                -G.gapC weight q e rho i
              else 0
            else 0) = -G.gapC weight q e rho i := by
          simp [hi, finitePathNext]
        unfold finiteSourcePathMatrix
        rw [ite_eq_right hij, hprevTerm, hnextTerm]
        simp [gapC]
      · have hkr : G.idx j ≠ G.idx i := G.idx.injective.ne hij
        have hnkr : next (G.idx j) ≠ G.idx i := by
          intro h
          exact hpred ((G.predecessor_support i j).mp h)
        have hkn : G.idx j ≠ next (G.idx i) := by
          intro h
          exact hsucc ((G.successor_support i j).mp h.symm)
        have hnkn : next (G.idx j) ≠ next (G.idx i) := by
          intro h
          exact hkr (next.injective h)
        rw [sourceOrderedCurrentMatrix_nonfork_off_support next weight back
          (G.nonfork i) (G.nonfork j) hkr hnkr hkn hnkn]
        have hprevTerm :
            (if h : 0 < i.val then
              if j = finitePathPrev i h then
                -(G.gapA p e i * G.gapS weight (finitePathPrev i h))
              else 0
            else 0) = 0 := by
          by_cases hp : 0 < i.val
          · rw [dite_eq_left hp, ite_eq_right (fun h => hpred ⟨hp, h⟩)]
          · rw [dite_eq_right hp]
        have hnextTerm :
            (if h : i.val < m then
              if j = finitePathNext i h then -G.gapC weight q e rho i else 0
            else 0) = 0 := by
          by_cases hn : i.val < m
          · rw [dite_eq_left hn, ite_eq_right (fun h => hsucc ⟨hn, h⟩)]
          · rw [dite_eq_right hn]
        unfold finiteSourcePathMatrix
        rw [ite_eq_right hij, hprevTerm, hnextTerm]
        ring

theorem gapA_nonneg (G : SourceGapEmbedding next back m)
    {p e : Fin n → ℝ} (hp : ∀ r, 0 ≤ p r) (he : ∀ r, 0 < e r) :
    ∀ i, 0 ≤ G.gapA p e i := by
  intro i
  exact div_nonneg (hp _) (le_of_lt (he _))

theorem gapC_nonneg (G : SourceGapEmbedding next back m)
    {weight : Fin n → ℕ} {q e rho : Fin n → ℝ}
    (hq : ∀ r, 0 ≤ q r) (he : ∀ r, 0 < e r)
    (hrho : ∀ r, 0 < rho r) (hw : ∀ r, 0 < weight r) :
    ∀ i, 0 ≤ G.gapC weight q e rho i := by
  intro i
  apply mul_nonneg (hq _)
  exact div_nonneg
    (le_of_lt (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)))
    (le_of_lt (he _))

theorem gapS_pos (G : SourceGapEmbedding next back m)
    {weight : Fin n → ℕ} (hw : ∀ r, 0 < weight r) :
    ∀ i, 0 < G.gapS weight i := by
  intro i
  unfold gapS
  exact_mod_cast hw (G.idx i)

theorem gapS_one_le (G : SourceGapEmbedding next back m)
    {weight : Fin n → ℕ} (hw : ∀ r, 0 < weight r) :
    ∀ i, 1 ≤ G.gapS weight i := by
  intro i
  unfold gapS
  exact_mod_cast hw (G.idx i)

/-- Every literal nonfork paper gap is invertible under the positive
mass-action hypotheses; hence a global kernel can only survive through the
remaining fork-to-fork Schur complement. -/
theorem restrictedCurrentMatrix_kernel_eq_zero
    (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (x : Fin (m + 1) → ℝ)
    (hker : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * x j = 0) :
    ∀ i, x i = 0 := by
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hker
  exact finiteSourcePathMatrix_kernel_eq_zero
    (G.gapA_nonneg hp he) (G.gapC_nonneg hq he hrho hw)
    (G.gapS_pos hw) x hker

/-- Source-level Green attenuation for one literal gap.  Any response to the
two endpoint forcings is bounded by the cumulative product of the literal
successor multiplicities. -/
theorem restrictedBoundaryResponse_le_weight
    (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    {y : Fin (m + 1) → ℝ} {scale : ℝ}
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 1 ≤ scale)
    (hsolve : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * y j =
        finiteSourcePathBoundaryForcing (G.gapA p e)
          (G.gapC weight q e rho) scale i) :
    ∀ i, y i ≤ scale * finiteSourcePathWeight (G.gapS weight) i := by
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hsolve
  exact finiteSourcePathBoundaryResponse_le_weight
    (G.gapA_nonneg hp he) (G.gapC_nonneg hq he hrho hw)
    (G.gapS_one_le hw) hscale hsolve

/-- The same literal gap response is nonnegative, giving the source-level
two-sided Green bound used in Schur elimination. -/
theorem restrictedBoundaryResponse_nonneg
    (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    {y : Fin (m + 1) → ℝ} {scale : ℝ}
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 ≤ scale)
    (hsolve : ∀ i,
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * y j =
        finiteSourcePathBoundaryForcing (G.gapA p e)
          (G.gapC weight q e rho) scale i) :
    ∀ i, 0 ≤ y i := by
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hsolve
  exact finiteSourcePathBoundaryResponse_nonneg
    (G.gapA_nonneg hp he) (G.gapC_nonneg hq he hrho hw)
    (G.gapS_pos hw) hscale hsolve

end SourceGapEmbedding

end TypeIIL

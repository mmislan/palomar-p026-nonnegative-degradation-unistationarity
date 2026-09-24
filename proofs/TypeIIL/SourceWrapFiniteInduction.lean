import proofs.TypeIIL.SourceWrapNatInduction

namespace TypeIIL

open scoped BigOperators

/-- Periodic total extension of a finite source-path vector.  The recurrence
only reads indices at most `m`; periodicity merely avoids irrelevant default
values and preserves positivity globally. -/
def finitePathNatLift {m : ℕ} (f : Fin (m + 1) → ℝ) (i : ℕ) : ℝ :=
  f ⟨i % (m + 1), Nat.mod_lt i (Nat.succ_pos m)⟩

theorem finitePathNatLift_of_lt {m i : ℕ} (f : Fin (m + 1) → ℝ)
    (hi : i < m + 1) :
    finitePathNatLift f i = f ⟨i, hi⟩ := by
  simp [finitePathNatLift, Nat.mod_eq_of_lt hi]

/-- Matrix-level docking of the inverse-free continuant induction.  The first
row is forced by the left fork; every strict interior row is homogeneous.
After eliminating the proper prefix, the remaining equation is the exact
condensed equation at the penultimate and terminal path coordinates. -/
theorem finiteSourcePath_properPrefixEquation
    {m : ℕ} (hm : 0 < m) (A c s x : Fin (m + 1) → ℝ)
    {scale k L : ℝ}
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i) (hs : ∀ i, 0 < s i)
    (hscale : 0 < scale) (hk : 0 < k)
    (hfirst :
      (∑ j, finiteSourcePathMatrix A c s 0 j * x j) =
        A 0 * scale * L)
    (hrows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
      ∑ j, finiteSourcePathMatrix A c s i j * x j = 0) :
    wrapFrontEquation
      (natWrapPrefixState (finitePathNatLift A) (finitePathNatLift c)
        (finitePathNatLift s) scale k (m - 1))
      (finitePathNatLift c (m - 1)) (finitePathNatLift s (m - 1)) L
      (finitePathNatLift x (m - 1)) (finitePathNatLift x m) := by
  have hnat :
      wrapFrontEquation
        (natWrapPrefixState (finitePathNatLift A) (finitePathNatLift c)
          (finitePathNatLift s) scale k (m - 1))
        (finitePathNatLift c (m - 1)) (finitePathNatLift s (m - 1)) L
        (finitePathNatLift x (m - 1)) (finitePathNatLift x (m - 1 + 1)) := by
    apply natWrapPrefixEquation (finitePathNatLift A) (finitePathNatLift c)
      (finitePathNatLift s) (finitePathNatLift x) (m - 1)
    · intro i
      exact hA _
    · intro i
      exact hc _
    · intro i
      exact hs _
    · exact hscale
    · exact hk
    · rw [finiteSourcePathMatrix_mul_apply] at hfirst
      simp only [Fin.val_zero, lt_self_iff_false] at hfirst
      unfold wrapFrontEquation natWrapPrefixState wrapPrefixPivot
      rw [finitePathNatLift_of_lt (i := 0) A (by omega),
        finitePathNatLift_of_lt (i := 0) c (by omega),
        finitePathNatLift_of_lt (i := 0) s (by omega),
        finitePathNatLift_of_lt (i := 0) x (by omega),
        finitePathNatLift_of_lt (i := 1) x (by omega)]
      have hzero : (0 : ℕ) < m := by omega
      simpa [finitePathNext, hzero, sub_eq_add_neg] using sub_eq_zero.mpr hfirst
    · intro i hi
      have him : i + 1 < m := by omega
      let fi : Fin (m + 1) := ⟨i + 1, by omega⟩
      have hrow := hrows fi (by simp [fi]) (by simpa [fi] using him)
      rw [finiteSourcePathMatrix_mul_apply] at hrow
      have hpos : 0 < fi.val := by simp [fi]
      have hnext : fi.val < m := by simpa [fi] using him
      simp only [hpos, hnext, dite_true] at hrow
      have hprevEq : finitePathPrev fi hpos = ⟨i, by omega⟩ := by
        apply Fin.ext
        simp [finitePathPrev, fi]
      have hnextEq : finitePathNext fi hnext = ⟨i + 2, by omega⟩ := by
        apply Fin.ext
        simp [finitePathNext, fi]
      rw [hprevEq, hnextEq] at hrow
      rw [finitePathNatLift_of_lt (i := i + 1) A (by omega),
        finitePathNatLift_of_lt (i := i) s (by omega),
        finitePathNatLift_of_lt (i := i) x (by omega),
        finitePathNatLift_of_lt (i := i + 1) c (by omega),
        finitePathNatLift_of_lt (i := i + 1) s (by omega),
        finitePathNatLift_of_lt (i := i + 1) x (by omega),
        finitePathNatLift_of_lt (i := i + 2) x (by omega)]
      simp only [fi] at hrow
      ring_nf at hrow ⊢
      exact hrow
  simpa only [show m - 1 + 1 = m by omega] using hnat

/-- The adjacent fork equation is condensed by the same finite-path prefix.
The accumulated scalar is the exact diagonal correction contributed by the
eliminated coordinates. -/
theorem finiteSourcePath_properPrefixForkEquation
    {m : ℕ} (hm : 0 < m) (A c s x : Fin (m + 1) → ℝ)
    {scale k L forkRest : ℝ}
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i) (hs : ∀ i, 0 < s i)
    (hscale : 0 < scale) (hk : 0 < k)
    (hfirst :
      (∑ j, finiteSourcePathMatrix A c s 0 j * x j) =
        A 0 * scale * L)
    (hrows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
      ∑ j, finiteSourcePathMatrix A c s i j * x j = 0)
    (hfork : forkRest - k * x 0 = 0) :
    forkRest -
        natWrapForkDiagonal (finitePathNatLift A) (finitePathNatLift c)
          (finitePathNatLift s) scale k (m - 1) * L -
        (natWrapPrefixState (finitePathNatLift A) (finitePathNatLift c)
          (finitePathNatLift s) scale k (m - 1)).k *
          finitePathNatLift x (m - 1) = 0 := by
  apply natWrapForkEquation (finitePathNatLift A) (finitePathNatLift c)
    (finitePathNatLift s) (finitePathNatLift x) (m - 1)
  · intro i
    exact hA _
  · intro i
    exact hc _
  · intro i
    exact hs _
  · exact hscale
  · exact hk
  · rw [finiteSourcePathMatrix_mul_apply] at hfirst
    simp only [Fin.val_zero, lt_self_iff_false] at hfirst
    unfold wrapFrontEquation natWrapPrefixState wrapPrefixPivot
    rw [finitePathNatLift_of_lt (i := 0) A (by omega),
      finitePathNatLift_of_lt (i := 0) c (by omega),
      finitePathNatLift_of_lt (i := 0) s (by omega),
      finitePathNatLift_of_lt (i := 0) x (by omega),
      finitePathNatLift_of_lt (i := 1) x (by omega)]
    have hzero : (0 : ℕ) < m := by omega
    simpa [finitePathNext, hzero, sub_eq_add_neg] using sub_eq_zero.mpr hfirst
  · intro i hi
    have him : i + 1 < m := by omega
    let fi : Fin (m + 1) := ⟨i + 1, by omega⟩
    have hrow := hrows fi (by simp [fi]) (by simpa [fi] using him)
    rw [finiteSourcePathMatrix_mul_apply] at hrow
    have hpos : 0 < fi.val := by simp [fi]
    have hnext : fi.val < m := by simpa [fi] using him
    simp only [hpos, hnext, dite_true] at hrow
    have hprevEq : finitePathPrev fi hpos = ⟨i, by omega⟩ := by
      apply Fin.ext
      simp [finitePathPrev, fi]
    have hnextEq : finitePathNext fi hnext = ⟨i + 2, by omega⟩ := by
      apply Fin.ext
      simp [finitePathNext, fi]
    rw [hprevEq, hnextEq] at hrow
    rw [finitePathNatLift_of_lt (i := i + 1) A (by omega),
      finitePathNatLift_of_lt (i := i) s (by omega),
      finitePathNatLift_of_lt (i := i) x (by omega),
      finitePathNatLift_of_lt (i := i + 1) c (by omega),
      finitePathNatLift_of_lt (i := i + 1) s (by omega),
      finitePathNatLift_of_lt (i := i + 1) x (by omega),
      finitePathNatLift_of_lt (i := i + 2) x (by omega)]
    simp only [fi] at hrow
    ring_nf at hrow ⊢
    exact hrow
  · simpa [finitePathNatLift_of_lt (i := 0) x (by omega)] using hfork

/-- Finite-path form of forward-flux conservation.  The reserved row
`m-1` may carry the mixed right-boundary forcing; only earlier homogeneous
rows are used. -/
theorem finiteSourcePath_forward_boundary_transport
    {m : ℕ} (hm : 0 < m) (A c s x : Fin (m + 1) → ℝ)
    {scale k : ℝ}
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i) (hs : ∀ i, 0 < s i)
    (hscale : 0 < scale) (hk : 0 < k)
    (hfirst : ∑ j, finiteSourcePathMatrix A c s 0 j * x j = 0)
    (hrows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m - 1 →
      ∑ j, finiteSourcePathMatrix A c s i j * x j = 0) :
    k * x 0 =
      (natWrapPrefixState (finitePathNatLift A) (finitePathNatLift c)
        (finitePathNatLift s) scale k (m - 1)).k *
          finitePathNatLift x (m - 1) := by
  apply natWrapForwardTransport (finitePathNatLift A) (finitePathNatLift c)
    (finitePathNatLift s) (finitePathNatLift x) (m - 1)
  · exact fun i => hA _
  · exact fun i => hc _
  · exact fun i => hs _
  · exact hscale
  · exact hk
  · rw [finiteSourcePathMatrix_mul_apply] at hfirst
    simp only [Fin.val_zero, lt_self_iff_false] at hfirst
    unfold wrapFrontEquation natWrapPrefixState wrapPrefixPivot
    rw [finitePathNatLift_of_lt (i := 0) A (by omega),
      finitePathNatLift_of_lt (i := 0) c (by omega),
      finitePathNatLift_of_lt (i := 0) s (by omega),
      finitePathNatLift_of_lt (i := 0) x (by omega),
      finitePathNatLift_of_lt (i := 1) x (by omega)]
    have hzero : (0 : ℕ) < m := by omega
    simpa [finitePathNext, hzero, sub_eq_add_neg] using sub_eq_zero.mpr hfirst
  · intro i hi
    have hir : i + 1 < m - 1 := hi
    let fi : Fin (m + 1) := ⟨i + 1, by omega⟩
    have hrow := hrows fi (by simp [fi]) (by simpa [fi] using hir)
    rw [finiteSourcePathMatrix_mul_apply] at hrow
    have hpos : 0 < fi.val := by simp [fi]
    have hinext : i + 1 < m := by omega
    have hnext : fi.val < m := by simpa [fi] using hinext
    simp only [hpos, hnext, dite_true] at hrow
    have hprevEq : finitePathPrev fi hpos = ⟨i, by omega⟩ := by
      apply Fin.ext
      simp [finitePathPrev, fi]
    have hnextEq : finitePathNext fi hnext = ⟨i + 2, by omega⟩ := by
      apply Fin.ext
      simp [finitePathNext, fi]
    rw [hprevEq, hnextEq] at hrow
    rw [finitePathNatLift_of_lt (i := i + 1) A (by omega),
      finitePathNatLift_of_lt (i := i) s (by omega),
      finitePathNatLift_of_lt (i := i) x (by omega),
      finitePathNatLift_of_lt (i := i + 1) c (by omega),
      finitePathNatLift_of_lt (i := i + 1) s (by omega),
      finitePathNatLift_of_lt (i := i + 1) x (by omega),
      finitePathNatLift_of_lt (i := i + 2) x (by omega)]
    simp only [fi] at hrow
    ring_nf at hrow ⊢
    exact hrow

/-- Literal source specialization of `finiteSourcePath_properPrefixEquation`.
No Schur inequality is assumed: the hypotheses are exactly the first forced
row and the homogeneous strict-interior rows of the restricted source-current
kernel. -/
theorem SourceGapEmbedding.restricted_properPrefixEquation
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (x : Fin (m + 1) → ℝ) {scale k L : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 < scale) (hk : 0 < k)
    (hfirst :
      (∑ j, G.restrictedCurrentMatrix weight p q e rho 0 j * x j) =
        G.gapA p e 0 * scale * L)
    (hrows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * x j = 0) :
    wrapFrontEquation
      (natWrapPrefixState (finitePathNatLift (G.gapA p e))
        (finitePathNatLift (G.gapC weight q e rho))
        (finitePathNatLift (G.gapS weight)) scale k (m - 1))
      (finitePathNatLift (G.gapC weight q e rho) (m - 1))
      (finitePathNatLift (G.gapS weight) (m - 1)) L
      (finitePathNatLift x (m - 1)) (finitePathNatLift x m) := by
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hfirst hrows
  apply finiteSourcePath_properPrefixEquation hm _ _ _ _
  · intro i
    exact div_pos (hp _) (he _)
  · intro i
    unfold SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  · exact G.gapS_pos hw
  · exact hscale
  · exact hk
  · exact hfirst
  · exact hrows

/-- Literal source specialization of the adjacent-fork prefix transport. -/
theorem SourceGapEmbedding.restricted_properPrefixForkEquation
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (x : Fin (m + 1) → ℝ) {scale k L forkRest : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 < scale) (hk : 0 < k)
    (hfirst :
      (∑ j, G.restrictedCurrentMatrix weight p q e rho 0 j * x j) =
        G.gapA p e 0 * scale * L)
    (hrows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * x j = 0)
    (hfork : forkRest - k * x 0 = 0) :
    forkRest -
        natWrapForkDiagonal (finitePathNatLift (G.gapA p e))
          (finitePathNatLift (G.gapC weight q e rho))
          (finitePathNatLift (G.gapS weight)) scale k (m - 1) * L -
        (natWrapPrefixState (finitePathNatLift (G.gapA p e))
          (finitePathNatLift (G.gapC weight q e rho))
          (finitePathNatLift (G.gapS weight)) scale k (m - 1)).k *
          finitePathNatLift x (m - 1) = 0 := by
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hfirst hrows
  apply finiteSourcePath_properPrefixForkEquation hm _ _ _ _
  · intro i
    exact div_pos (hp _) (he _)
  · intro i
    unfold SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  · exact G.gapS_pos hw
  · exact hscale
  · exact hk
  · exact hfirst
  · exact hrows
  · exact hfork

/-- Literal source specialization of forward-boundary transport. -/
theorem SourceGapEmbedding.restricted_forward_boundary_transport
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (x : Fin (m + 1) → ℝ) {scale k : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 < scale) (hk : 0 < k)
    (hfirst : ∑ j, G.restrictedCurrentMatrix weight p q e rho 0 j * x j = 0)
    (hrows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m - 1 →
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * x j = 0) :
    k * x 0 =
      (natWrapPrefixState (finitePathNatLift (G.gapA p e))
        (finitePathNatLift (G.gapC weight q e rho))
        (finitePathNatLift (G.gapS weight)) scale k (m - 1)).k *
        finitePathNatLift x (m - 1) := by
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hfirst hrows
  exact finiteSourcePath_forward_boundary_transport hm
      (G.gapA p e) (G.gapC weight q e rho) (G.gapS weight) x
      (fun i => div_pos (hp _) (he _))
      (by
        intro i
        unfold SourceGapEmbedding.gapC
        exact mul_pos (hq _) (div_pos
          (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _)))
      (G.gapS_pos hw) hscale hk hfirst hrows

/-- Matrix-level affine docking for the exceptional mixed column.  Earlier
strict-interior rows are homogeneous, while the penultimate row carries the
single nonzero forcing that survives into the condensed two-node system. -/
theorem finiteSourcePath_properPrefixEquation_final_rhs
    {m : ℕ} (hm : 1 < m) (A c s x : Fin (m + 1) → ℝ)
    {scale k L rhs : ℝ}
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i) (hs : ∀ i, 0 < s i)
    (hscale : 0 < scale) (hk : 0 < k)
    (hfirst :
      (∑ j, finiteSourcePathMatrix A c s 0 j * x j) =
        A 0 * scale * L)
    (hrows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m - 1 →
      ∑ j, finiteSourcePathMatrix A c s i j * x j = 0)
    (hfinal :
      ∑ j, finiteSourcePathMatrix A c s ⟨m - 1, by omega⟩ j * x j = rhs) :
    (1 +
        (natWrapPrefixState (finitePathNatLift A) (finitePathNatLift c)
          (finitePathNatLift s) scale k (m - 1)).A +
          finitePathNatLift c (m - 1) * finitePathNatLift s (m - 1)) *
        finitePathNatLift x (m - 1) -
      finitePathNatLift c (m - 1) * finitePathNatLift x m -
      (natWrapPrefixState (finitePathNatLift A) (finitePathNatLift c)
        (finitePathNatLift s) scale k (m - 1)).A *
        (natWrapPrefixState (finitePathNatLift A) (finitePathNatLift c)
          (finitePathNatLift s) scale k (m - 1)).scale * L = rhs := by
  have hnat := natWrapPrefixEquation_final_rhs
    (finitePathNatLift A) (finitePathNatLift c) (finitePathNatLift s)
    (finitePathNatLift x) (L := L) (rhs := rhs) (m - 2)
    (fun i => hA _) (fun i => hc _) (fun i => hs _) hscale hk
  have hfirst' :
      wrapFrontEquation
        (natWrapPrefixState (finitePathNatLift A) (finitePathNatLift c)
          (finitePathNatLift s) scale k 0)
        (finitePathNatLift c 0) (finitePathNatLift s 0) L
        (finitePathNatLift x 0) (finitePathNatLift x 1) := by
    rw [finiteSourcePathMatrix_mul_apply] at hfirst
    simp only [Fin.val_zero, lt_self_iff_false] at hfirst
    unfold wrapFrontEquation natWrapPrefixState wrapPrefixPivot
    rw [finitePathNatLift_of_lt (i := 0) A (by omega),
      finitePathNatLift_of_lt (i := 0) c (by omega),
      finitePathNatLift_of_lt (i := 0) s (by omega),
      finitePathNatLift_of_lt (i := 0) x (by omega),
      finitePathNatLift_of_lt (i := 1) x (by omega)]
    have hzero : (0 : ℕ) < m := by omega
    simpa [finitePathNext, hzero, sub_eq_add_neg] using sub_eq_zero.mpr hfirst
  have hrows' : ∀ i < m - 2,
      (-finitePathNatLift A (i + 1) * finitePathNatLift s i) *
          finitePathNatLift x i +
        (1 + finitePathNatLift A (i + 1) +
            finitePathNatLift c (i + 1) * finitePathNatLift s (i + 1)) *
          finitePathNatLift x (i + 1) -
        finitePathNatLift c (i + 1) * finitePathNatLift x (i + 2) = 0 := by
    intro i hi
    have him : i + 1 < m - 1 := by omega
    let fi : Fin (m + 1) := ⟨i + 1, by omega⟩
    have hrow := hrows fi (by simp [fi]) (by simpa [fi] using him)
    rw [finiteSourcePathMatrix_mul_apply] at hrow
    have hpos : 0 < fi.val := by simp [fi]
    have hnextNat : i + 1 < m := lt_trans him (by omega)
    have hnext : fi.val < m := by simpa [fi] using hnextNat
    simp only [hpos, hnext, dite_true] at hrow
    have hprevEq : finitePathPrev fi hpos = ⟨i, by omega⟩ := by
      apply Fin.ext
      simp [finitePathPrev, fi]
    have hnextEq : finitePathNext fi hnext = ⟨i + 2, by omega⟩ := by
      apply Fin.ext
      simp [finitePathNext, fi]
    rw [hprevEq, hnextEq] at hrow
    rw [finitePathNatLift_of_lt (i := i + 1) A (by omega),
      finitePathNatLift_of_lt (i := i) s (by omega),
      finitePathNatLift_of_lt (i := i) x (by omega),
      finitePathNatLift_of_lt (i := i + 1) c (by omega),
      finitePathNatLift_of_lt (i := i + 1) s (by omega),
      finitePathNatLift_of_lt (i := i + 1) x (by omega),
      finitePathNatLift_of_lt (i := i + 2) x (by omega)]
    simp only [fi] at hrow
    ring_nf at hrow ⊢
    exact hrow
  have hfinal' :
      (-finitePathNatLift A (m - 2 + 1) * finitePathNatLift s (m - 2)) *
          finitePathNatLift x (m - 2) +
        (1 + finitePathNatLift A (m - 2 + 1) +
            finitePathNatLift c (m - 2 + 1) *
              finitePathNatLift s (m - 2 + 1)) *
          finitePathNatLift x (m - 2 + 1) -
        finitePathNatLift c (m - 2 + 1) *
          finitePathNatLift x (m - 2 + 2) = rhs := by
    simp only [show m - 2 + 1 = m - 1 by omega,
      show m - 2 + 2 = m by omega]
    let fi : Fin (m + 1) := ⟨m - 1, by omega⟩
    have hf := hfinal
    change (∑ j, finiteSourcePathMatrix A c s fi j * x j) = rhs at hf
    rw [finiteSourcePathMatrix_mul_apply] at hf
    have hpos : 0 < fi.val := by simp [fi]; omega
    have hnext : fi.val < m := by simp [fi]; omega
    simp only [hpos, hnext, dite_true] at hf
    have hprevEq : finitePathPrev fi hpos = ⟨m - 2, by omega⟩ := by
      apply Fin.ext
      simp [finitePathPrev, fi]
      omega
    have hnextEq : finitePathNext fi hnext = ⟨m, by omega⟩ := by
      apply Fin.ext
      simp [finitePathNext, fi]
      omega
    rw [hprevEq, hnextEq] at hf
    rw [finitePathNatLift_of_lt (i := m - 1) A (by omega),
      finitePathNatLift_of_lt (i := m - 2) s (by omega),
      finitePathNatLift_of_lt (i := m - 2) x (by omega),
      finitePathNatLift_of_lt (i := m - 1) c (by omega),
      finitePathNatLift_of_lt (i := m - 1) s (by omega),
      finitePathNatLift_of_lt (i := m - 1) x (by omega),
      finitePathNatLift_of_lt (i := m) x (by omega)]
    simp only [fi] at hf
    ring_nf at hf ⊢
    exact hf
  have hout := hnat hfirst' hrows' hfinal'
  simpa only [show m - 2 + 1 = m - 1 by omega,
    show m - 2 + 2 = m by omega] using hout

/-- Literal source specialization of the affine penultimate-row transport. -/
theorem SourceGapEmbedding.restricted_properPrefixEquation_final_rhs
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (hm : 1 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (x : Fin (m + 1) → ℝ) {scale k L rhs : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 < scale) (hk : 0 < k)
    (hfirst :
      (∑ j, G.restrictedCurrentMatrix weight p q e rho 0 j * x j) =
        G.gapA p e 0 * scale * L)
    (hrows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m - 1 →
      ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * x j = 0)
    (hfinal :
      ∑ j, G.restrictedCurrentMatrix weight p q e rho
        ⟨m - 1, by omega⟩ j * x j = rhs) :
    (1 +
        (natWrapPrefixState (finitePathNatLift (G.gapA p e))
          (finitePathNatLift (G.gapC weight q e rho))
          (finitePathNatLift (G.gapS weight)) scale k (m - 1)).A +
          finitePathNatLift (G.gapC weight q e rho) (m - 1) *
            finitePathNatLift (G.gapS weight) (m - 1)) *
        finitePathNatLift x (m - 1) -
      finitePathNatLift (G.gapC weight q e rho) (m - 1) *
        finitePathNatLift x m -
      (natWrapPrefixState (finitePathNatLift (G.gapA p e))
        (finitePathNatLift (G.gapC weight q e rho))
        (finitePathNatLift (G.gapS weight)) scale k (m - 1)).A *
        (natWrapPrefixState (finitePathNatLift (G.gapA p e))
          (finitePathNatLift (G.gapC weight q e rho))
          (finitePathNatLift (G.gapS weight)) scale k (m - 1)).scale * L = rhs := by
  rw [G.restrictedCurrentMatrix_eq_finiteSourcePathMatrix] at hfirst hrows hfinal
  apply finiteSourcePath_properPrefixEquation_final_rhs hm _ _ _ _
  · intro i
    exact div_pos (hp _) (he _)
  · intro i
    unfold SourceGapEmbedding.gapC
    exact mul_pos (hq _) (div_pos
      (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _))
  · exact G.gapS_pos hw
  · exact hscale
  · exact hk
  · exact hfirst
  · exact hrows
  · exact hfinal

/-- Literal finite-gap specialization of the grouped adjacent-fork budget.
The accumulated prefix correction plus the surviving terminal boundary
product never exceeds the original direct fork product. -/
theorem SourceGapEmbedding.properWrapForkDiagonal_add_terminal_le_initial
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    {scale k : ℝ}
    (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r) (hscale : 0 < scale) (hk : 0 < k) :
    natWrapForkDiagonal (finitePathNatLift (G.gapA p e))
          (finitePathNatLift (G.gapC weight q e rho))
          (finitePathNatLift (G.gapS weight)) scale k (m - 1) +
        (natWrapPrefixState (finitePathNatLift (G.gapA p e))
          (finitePathNatLift (G.gapC weight q e rho))
          (finitePathNatLift (G.gapS weight)) scale k (m - 1)).k *
        (natWrapPrefixState (finitePathNatLift (G.gapA p e))
          (finitePathNatLift (G.gapC weight q e rho))
          (finitePathNatLift (G.gapS weight)) scale k (m - 1)).scale ≤
      k * scale := by
  have hnat := natWrapForkDiagonal_add_terminal_le_initial
    (finitePathNatLift (G.gapA p e))
    (finitePathNatLift (G.gapC weight q e rho))
    (finitePathNatLift (G.gapS weight))
    (fun i => div_pos (hp _) (he _))
    (by
      intro i
      unfold SourceGapEmbedding.gapC
      exact mul_pos (hq _) (div_pos
        (TypeII3.secantPoly_pos (hrho _) (by norm_num) (hw _)) (he _)))
    (fun i => G.gapS_pos hw _) hscale hk (m - 1)
  exact hnat

/-- Finite-path form of the arbitrary-gap left diagonal budget.  The actual
direct boundary term plus the mixed left response dominates the condensed
endpoint core. -/
theorem finiteSourcePath_left_diagonal_core_le
    {m : ℕ} (hm : 0 < m) (A c s x : Fin (m + 1) → ℝ)
    {scale k : ℝ}
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i) (hs : ∀ i, 0 < s i)
    (hscale : 0 < scale) (hk : 0 < k)
    (hunit : s (Fin.last m) = 1)
    (hfirst : ∑ j, finiteSourcePathMatrix A c s 0 j * x j =
      -(A 0 * scale))
    (hrows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
      ∑ j, finiteSourcePathMatrix A c s i j * x j = 0)
    (hterminal :
      ∑ j, finiteSourcePathMatrix A c s (Fin.last m) j * x j = 0) :
    let eff := natWrapPrefixState (finitePathNatLift A) (finitePathNatLift c)
      (finitePathNatLift s) scale k (m - 1)
    let Aeff := wrapCondensedA eff.A (finitePathNatLift A m)
      (finitePathNatLift c (m - 1)) (finitePathNatLift s (m - 1))
    let seff := wrapCondensedScale eff.A (finitePathNatLift s (m - 1)) eff.scale
    let keff := wrapCondensedK eff.A (finitePathNatLift c (m - 1))
      (finitePathNatLift s (m - 1)) eff.k
    let d := 1 + Aeff + finitePathNatLift c m
    (d + keff * seff * (1 + finitePathNatLift c m)) / d ≤
      1 + k * scale + k * x 0 := by
  let eff := natWrapPrefixState (finitePathNatLift A) (finitePathNatLift c)
    (finitePathNatLift s) scale k (m - 1)
  have hfront := finiteSourcePath_properPrefixEquation hm A c s x
    hA hc hs hscale hk (L := -1) (by simpa using hfirst) hrows
  have hfork := finiteSourcePath_properPrefixForkEquation hm A c s x
    hA hc hs hscale hk (L := -1) (forkRest := k * x 0)
    (by simpa using hfirst) hrows (by ring)
  have hbudget := natWrapForkDiagonal_add_terminal_le_initial
    (finitePathNatLift A) (finitePathNatLift c) (finitePathNatLift s)
    (fun i => hA _) (fun i => hc _) (fun i => hs _) hscale hk (m - 1)
  have hpos := natWrapPrefixState_pos
    (finitePathNatLift A) (finitePathNatLift c) (finitePathNatLift s)
    (fun i => hA _) (fun i => hc _) (fun i => hs _) hscale hk (m - 1)
  have hterm :
      -(finitePathNatLift A m * finitePathNatLift s (m - 1)) *
          finitePathNatLift x (m - 1) +
        (1 + finitePathNatLift A m + finitePathNatLift c m) *
          finitePathNatLift x m = 0 := by
    rw [finiteSourcePathMatrix_mul_apply] at hterminal
    simp only [Fin.val_last, hm, dite_true, lt_self_iff_false, dite_false] at hterminal
    rw [hunit] at hterminal
    have hprev : finitePathPrev (Fin.last m) hm = ⟨m - 1, by omega⟩ := by
      apply Fin.ext
      simp [finitePathPrev]
    rw [hprev] at hterminal
    have hlast : (Fin.last m : Fin (m + 1)) = ⟨m, by omega⟩ := by
      apply Fin.ext
      simp
    rw [hlast] at hterminal
    simp only [finitePathNatLift_of_lt (i := m) A (by omega),
      finitePathNatLift_of_lt (i := m - 1) s (by omega),
      finitePathNatLift_of_lt (i := m - 1) x (by omega),
      finitePathNatLift_of_lt (i := m) c (by omega),
      finitePathNatLift_of_lt (i := m) x (by omega)]
    linarith [hterminal]
  have hrow₀ :
      wrapPrefixPivot eff.A (finitePathNatLift c (m - 1))
          (finitePathNatLift s (m - 1)) * finitePathNatLift x (m - 1) -
        finitePathNatLift c (m - 1) * finitePathNatLift x m =
          -(eff.A * eff.scale) := by
    change wrapFrontEquation eff _ _ (-1) _ _ at hfront
    unfold wrapFrontEquation at hfront
    linarith
  have htwo := two_reaction_left_diagonal_budget_eq hpos.1
    (by exact hA _) (by exact hc _) (by exact hc _) (by exact hs _)
    hrow₀ hterm (scale := eff.scale) (k := eff.k)
  have hrem : 0 ≤ eff.k * eff.scale / (1 + eff.A) := by
    exact div_nonneg
      (mul_nonneg (le_of_lt hpos.2.2) (le_of_lt hpos.2.1))
      (by linarith [hpos.1])
  dsimp only at htwo ⊢
  change k * x 0 - natWrapForkDiagonal (finitePathNatLift A)
    (finitePathNatLift c) (finitePathNatLift s) scale k (m - 1) * (-1) -
      eff.k * finitePathNatLift x (m - 1) = 0 at hfork
  change natWrapForkDiagonal (finitePathNatLift A) (finitePathNatLift c)
      (finitePathNatLift s) scale k (m - 1) + eff.k * eff.scale ≤
    k * scale at hbudget
  linarith

end TypeIIL

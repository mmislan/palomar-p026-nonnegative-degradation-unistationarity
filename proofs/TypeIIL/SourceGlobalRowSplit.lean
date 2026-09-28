module

public import proofs.TypeIIL.SourceWrapKernelElimination

@[expose] public section

namespace TypeIIL

open scoped BigOperators

/-- A finite sum supported on an embedded block and two exterior points splits
into exactly those three pieces. -/
theorem sum_eq_embedding_sum_add_two
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (idx : α ↪ β) (left right : β) (f : β → ℝ)
    (hleft : ∀ i, left ≠ idx i) (hright : ∀ i, right ≠ idx i)
    (hlr : left ≠ right)
    (hzero : ∀ k, k ≠ left → k ≠ right → (∀ i, k ≠ idx i) → f k = 0) :
    (∑ k, f k) = (∑ i, f (idx i)) + f left + f right := by
  classical
  let range : Finset β := Finset.univ.map idx
  have hleftRange : left ∉ range := by
    simp only [range, Finset.mem_map, Finset.mem_univ, true_and, not_exists]
    exact fun i => (hleft i).symm
  have hrightRange : right ∉ range := by
    simp only [range, Finset.mem_map, Finset.mem_univ, true_and, not_exists]
    exact fun i => (hright i).symm
  calc
    ∑ k, f k = ∑ k ∈ insert left (insert right range), f k := by
      symm
      apply Finset.sum_subset (by simp)
      intro k _ hk
      apply hzero k
      · intro hkl
        apply hk
        simp [hkl]
      · intro hkr
        apply hk
        simp [hkr]
      · intro i hki
        apply hk
        simp [range, hki]
    _ = f left + f right + ∑ i, f (idx i) := by
      rw [Finset.sum_insert, Finset.sum_insert]
      · rw [Finset.sum_map]
        ring
      · exact hrightRange
      · simp [hlr, hleftRange]
    _ = (∑ i, f (idx i)) + f left + f right := by ring

/-- Pure source-incidence condition needed to isolate one literal gap inside
the full current matrix.  It asserts no coefficient identity: an exterior
reaction has neither the gap-row species nor its successor in its source or
product support. -/
structure SourceWrapGlobalColumnClosed
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    (P : SourceWrapForkGap G left right leftBack) : Prop where
  outside_support : ∀ (i : Fin (m + 1)) (k : Fin n),
    k ≠ left → k ≠ right → (∀ j, k ≠ G.idx j) →
      (G.idx i ≠ k ∧ G.idx i ≠ next k ∧
        (∀ z, back k = some z → G.idx i ≠ z)) ∧
      (next (G.idx i) ≠ k ∧ next (G.idx i) ≠ next k ∧
        (∀ z, back k = some z → next (G.idx i) ≠ z))

theorem SourceWrapGlobalColumnClosed.entry_zero
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    {P : SourceWrapForkGap G left right leftBack}
    (H : SourceWrapGlobalColumnClosed P)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (i : Fin (m + 1)) (k : Fin n)
    (hkl : k ≠ left) (hkr : k ≠ right) (hkg : ∀ j, k ≠ G.idx j) :
    currentSecantKernelMatrixWith
        (orderedMonomialSecantMatrix
          (sourceProductExponent next weight back) rho)
        (sourceStoich next weight back) p q e (G.idx i) k = 0 := by
  obtain ⟨⟨hrk, hrn, hrb⟩, ⟨hnk, hnn, hnb⟩⟩ :=
    H.outside_support i k hkl hkr hkg
  rw [sourceOrderedCurrentMatrix_nonfork_entry next weight back (G.nonfork i)]
  rw [ite_eq_right hrk]
  rw [sourceStoich_eq_zero_of_off_support next weight back hrk hrn hrb]
  rw [sourceStoich_eq_zero_of_off_support next weight back hnk hnn hnb]
  ring

/-- The full source-current kernel row splits into its literal gap block and
the two adjacent fork columns under the pure incidence condition above. -/
theorem SourceWrapGlobalColumnClosed.kernel_row_split
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    {P : SourceWrapForkGap G left right leftBack}
    (H : SourceWrapGlobalColumnClosed P)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (x : Fin n → ℝ)
    (hker : ∀ r, ∑ k,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e r k * x k = 0) :
    ∀ i,
      (∑ j, G.restrictedCurrentMatrix weight p q e rho i j * x (G.idx j)) +
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e (G.idx i) left * x left +
        currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e (G.idx i) right * x right = 0 := by
  intro i
  let M := currentSecantKernelMatrixWith
    (orderedMonomialSecantMatrix (sourceProductExponent next weight back) rho)
    (sourceStoich next weight back) p q e
  have hsum := sum_eq_embedding_sum_add_two G.idx left right
    (fun k => M (G.idx i) k * x k)
    (fun j => (P.post.fork_outside j))
    (fun j => (P.pre.fork_ne_idx j)) P.left_ne_right
    (fun k hkl hkr hkg => by
      have he0 := H.entry_zero weight p q e rho i k hkl hkr hkg
      change M (G.idx i) k = 0 at he0
      change M (G.idx i) k * x k = 0
      rw [he0]
      ring)
  have hk := hker (G.idx i)
  change (∑ k, M (G.idx i) k * x k) = 0 at hk
  change (∑ j, M (G.idx i) (G.idx j) * x (G.idx j)) +
      M (G.idx i) left * x left + M (G.idx i) right * x right = 0
  rw [← hsum]
  exact hk

/-- A full source-current kernel therefore reconstructs on every globally
closed long gap from the two literal Schur responses. -/
theorem SourceWrapGlobalColumnClosed.internal_coordinates_eq_negative_responses_of_kernel
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    {G : SourceGapEmbedding next back m} {left right leftBack : Fin n}
    {P : SourceWrapForkGap G left right leftBack}
    (H : SourceWrapGlobalColumnClosed P) (hm : 0 < m)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : weight (G.idx (Fin.last m)) = 1)
    (x : Fin n → ℝ) (xf yw : Fin (m + 1) → ℝ)
    (hxf : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * xf j =
      sourceWrapForwardForcing (G.gapA p e)
        (G.gapC weight q e rho) i)
    (hyw : ∀ i, ∑ j, G.restrictedCurrentMatrix weight p q e rho i j * yw j =
      sourceWrapLeftForcing (G.gapA p e) (weight left) i)
    (hker : ∀ r, ∑ k,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e r k * x k = 0) :
    ∀ i, x (G.idx i) = -(yw i * x left + xf i * x right) := by
  apply P.internal_coordinates_eq_negative_responses hm weight p q e rho
    hp hq he hrho hw hunit x xf yw hxf hyw
  exact H.kernel_row_split weight p q e rho x hker

end TypeIIL

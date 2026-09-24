import proofs.TypeIIL.SourceGlobalRowSplit

namespace TypeIIL

/-- Paper-shaped cyclic decomposition into forks and nonempty intervening
nonfork gaps.  The `wrap` fields encode only literal successor/back incidence;
`cover` and `gap_owner` say these pieces partition the reaction cycle. -/
structure SourceCyclicNonemptyGapSystem
    {n l : ℕ} (next : Fin n ≃ Fin n) (back : Fin n → Option (Fin n)) where
  step : Fin l ≃ Fin l
  /-- The fork successor is one cycle, presented in the paper's cyclic order.
  Keeping the enumeration explicit avoids silently treating an arbitrary
  permutation as a connected cycle in determinant and transfer arguments. -/
  cyclicOrder : Fin l ≃ Fin l
  step_cyclicOrder : ∀ i,
    step (cyclicOrder i) = cyclicOrder (finRotate l i)
  fork : Fin l ↪ Fin n
  gapLength : Fin l → ℕ
  gap : ∀ j, SourceGapEmbedding next back (gapLength j)
  wrap : ∀ j,
    SourceWrapForkGap (gap j) (fork j) (fork (step j))
      ((gap (step.symm j)).idx (Fin.last (gapLength (step.symm j))))
  cover : ∀ k : Fin n,
    (∃ j, k = fork j) ∨
      ∃ j, ∃ i : Fin (gapLength j + 1), k = (gap j).idx i
  fork_ne_gap : ∀ a b, ∀ i : Fin (gapLength b + 1),
    fork a ≠ (gap b).idx i
  gap_owner : ∀ a b, ∀ i : Fin (gapLength a + 1),
      ∀ k : Fin (gapLength b + 1),
    (gap a).idx i = (gap b).idx k → a = b

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

/-- Rotate the paper's cyclic fork enumeration so that `start` is index zero. -/
noncomputable def cyclicOrderFrom [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (start : Fin l) : Fin l ≃ Fin l :=
  (Equiv.addRight (S.cyclicOrder.symm start)).trans S.cyclicOrder

@[simp] theorem cyclicOrderFrom_zero [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (start : Fin l) : S.cyclicOrderFrom start 0 = start := by
  simp [cyclicOrderFrom]

/-- Every rotated enumeration still identifies `step` with canonical cyclic
successor.  This lets a proper determinant vertex be cut at whichever
predecessor column is absent. -/
theorem step_cyclicOrderFrom [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (start i : Fin l) :
    S.step (S.cyclicOrderFrom start i) =
      S.cyclicOrderFrom start (finRotate l i) := by
  rw [cyclicOrderFrom, Equiv.trans_apply, S.step_cyclicOrder]
  apply S.cyclicOrder.injective
  simp [Equiv.addRight, finRotate_apply, add_assoc, add_comm, add_left_comm]

/-- Natural-number view of a rotated cyclic enumeration. -/
noncomputable def cyclicIndexFrom [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (start : Fin l) (k : ℕ) : Fin l :=
  S.cyclicOrderFrom start (Fin.ofNat l k)

@[simp] theorem cyclicIndexFrom_zero [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (start : Fin l) : S.cyclicIndexFrom start 0 = start := by
  simp [cyclicIndexFrom]

theorem step_cyclicIndexFrom [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (start : Fin l) (k : ℕ) :
    S.step (S.cyclicIndexFrom start k) =
      S.cyclicIndexFrom start (k + 1) := by
  rw [cyclicIndexFrom, S.step_cyclicOrderFrom]
  unfold cyclicIndexFrom
  congr 1
  rw [finRotate_apply]
  simp only [Fin.ofNat_eq_cast]
  apply Fin.ext
  simp [Fin.val_add, Nat.add_mod]

/-- A full traversal in the rotated paper order returns to its starting
fork.  This is the endpoint identity needed by the cyclic continuant
adapter. -/
theorem cyclicIndexFrom_length [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (start : Fin l) :
    S.cyclicIndexFrom start l = start := by
  unfold cyclicIndexFrom
  have hmod : Fin.ofNat l l = 0 := by
    apply Fin.ext
    simp [Fin.ofNat]
  rw [hmod]
  exact S.cyclicOrderFrom_zero start

/-- Every non-start fork occurs at a unique positive natural index before
the end of one cyclic traversal. -/
theorem exists_cyclicIndexFrom_eq_of_ne [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (start a : Fin l) (ha : a ≠ start) :
    ∃ k, 1 ≤ k ∧ k < l ∧ S.cyclicIndexFrom start k = a := by
  let i : Fin l := (S.cyclicOrderFrom start).symm a
  have hidx : S.cyclicIndexFrom start i.val = a := by
    unfold cyclicIndexFrom
    have hfin : Fin.ofNat l i.val = i := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
    rw [hfin]
    exact (S.cyclicOrderFrom start).apply_symm_apply a
  refine ⟨i.val, ?_, i.isLt, hidx⟩
  by_contra hi
  have hi0 : i.val = 0 := by omega
  have hstart : S.cyclicIndexFrom start i.val = start := by
    rw [hi0, S.cyclicIndexFrom_zero]
  exact ha (hidx ▸ hstart)

/-- A genuine cyclic enumeration with at least two forks has no fixed step. -/
theorem ne_step_of_two_le [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 2 ≤ l) (a : Fin l) : a ≠ S.step a := by
  intro ha
  have h01 : S.cyclicIndexFrom a 0 = S.cyclicIndexFrom a 1 := by
    calc
      S.cyclicIndexFrom a 0 = a := S.cyclicIndexFrom_zero a
      _ = S.step a := ha
      _ = S.step (S.cyclicIndexFrom a 0) := by rw [S.cyclicIndexFrom_zero]
      _ = S.cyclicIndexFrom a 1 := by
        simpa using S.step_cyclicIndexFrom a 0
  unfold cyclicIndexFrom at h01
  have hfin : Fin.ofNat l 0 = Fin.ofNat l 1 :=
    (S.cyclicOrderFrom a).injective h01
  have hv := congrArg Fin.val hfin
  simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega : 1 < l)] at hv

/-- The last entry before returning to `start` is its cyclic predecessor. -/
theorem cyclicIndexFrom_pred_length [NeZero l]
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 1 ≤ l) (start : Fin l) :
    S.cyclicIndexFrom start (l - 1) = S.step.symm start := by
  apply S.step.injective
  rw [S.step_cyclicIndexFrom]
  have hsub : l - 1 + 1 = l := by omega
  rw [hsub, S.cyclicIndexFrom_length, S.step.apply_symm_apply]

theorem back_fork
    (S : SourceCyclicNonemptyGapSystem next back) (a : Fin l) :
    back (S.fork a) = some
      ((S.gap (S.step.symm a)).idx
        (Fin.last (S.gapLength (S.step.symm a)))) := by
  have h := (S.wrap (S.step.symm a)).pre.fork_back
  simpa using h

theorem next_gap_point_cases
    (S : SourceCyclicNonemptyGapSystem next back)
    (a : Fin l) (i : Fin (S.gapLength a + 1)) :
    (∃ k : Fin (S.gapLength a + 1),
      next ((S.gap a).idx i) = (S.gap a).idx k) ∨
      next ((S.gap a).idx i) = S.fork (S.step a) := by
  by_cases hi : i.val < S.gapLength a
  · exact Or.inl ⟨finitePathNext i hi, (S.gap a).idx_step i hi⟩
  · have hieq : i = Fin.last (S.gapLength a) := by
      apply Fin.ext
      simp
      omega
    subst i
    exact Or.inr (S.wrap a).pre.terminal_next

theorem gap_point_ne_other_gap
    (S : SourceCyclicNonemptyGapSystem next back)
    {a b : Fin l} (hab : a ≠ b)
    (i : Fin (S.gapLength a + 1)) (k : Fin (S.gapLength b + 1)) :
    (S.gap a).idx i ≠ (S.gap b).idx k := by
  intro h
  exact hab (S.gap_owner a b i k h)

theorem gap_point_ne_fork
    (S : SourceCyclicNonemptyGapSystem next back)
    (a b : Fin l) (i : Fin (S.gapLength b + 1)) :
    (S.gap b).idx i ≠ S.fork a :=
  (S.fork_ne_gap a b i).symm

/-- The paper-shaped cyclic partition implies the pure column-incidence
closure required by the global Schur row split. -/
theorem globalColumnClosed
    (S : SourceCyclicNonemptyGapSystem next back) (j : Fin l) :
    SourceWrapGlobalColumnClosed (S.wrap j) := by
  constructor
  intro i k hkl hkr hkg
  rcases S.cover k with ⟨a, rfl⟩ | ⟨a, t, rfl⟩
  · have haj : a ≠ j := by
      intro h
      subst a
      exact hkl rfl
    have haStep : a ≠ S.step j := by
      intro h
      subst a
      exact hkr rfl
    have hpred : S.step.symm a ≠ j := by
      intro h
      apply haStep
      calc
        a = S.step (S.step.symm a) := (S.step.apply_symm_apply a).symm
        _ = S.step j := congrArg S.step h
    have hrow :
        (S.gap j).idx i ≠ S.fork a ∧
        (S.gap j).idx i ≠ next (S.fork a) ∧
        (∀ z, back (S.fork a) = some z → (S.gap j).idx i ≠ z) := by
      refine ⟨S.gap_point_ne_fork a j i, ?_, ?_⟩
      · rw [← (S.wrap a).post.first_eq]
        exact S.gap_point_ne_other_gap haj.symm i 0
      · intro z hz
        rw [S.back_fork a] at hz
        injection hz with hz
        subst z
        exact S.gap_point_ne_other_gap hpred.symm i
          (Fin.last (S.gapLength (S.step.symm a)))
    have hnext :
        next ((S.gap j).idx i) ≠ S.fork a ∧
        next ((S.gap j).idx i) ≠ next (S.fork a) ∧
        (∀ z, back (S.fork a) = some z →
          next ((S.gap j).idx i) ≠ z) := by
      rcases S.next_gap_point_cases j i with ⟨u, hu⟩ | hu
      · rw [hu]
        refine ⟨S.gap_point_ne_fork a j u, ?_, ?_⟩
        · rw [← (S.wrap a).post.first_eq]
          exact S.gap_point_ne_other_gap haj.symm u 0
        · intro z hz
          rw [S.back_fork a] at hz
          injection hz with hz
          subst z
          exact S.gap_point_ne_other_gap hpred.symm u
            (Fin.last (S.gapLength (S.step.symm a)))
      · rw [hu]
        refine ⟨?_, ?_, ?_⟩
        · intro h
          exact haStep (S.fork.injective h.symm)
        · rw [← (S.wrap a).post.first_eq]
          exact S.fork_ne_gap (S.step j) a 0
        · intro z hz
          rw [S.back_fork a] at hz
          injection hz with hz
          subst z
          exact S.fork_ne_gap (S.step j) (S.step.symm a)
            (Fin.last (S.gapLength (S.step.symm a)))
    exact ⟨hrow, hnext⟩
  · have haj : a ≠ j := by
      intro h
      subst a
      exact hkg t rfl
    have hbackNone : ∀ z, back ((S.gap a).idx t) = some z → False := by
      intro z hz
      rw [(S.gap a).nonfork t] at hz
      contradiction
    have hrowNext : (S.gap j).idx i ≠ next ((S.gap a).idx t) := by
      rcases S.next_gap_point_cases a t with ⟨u, hu⟩ | hu
      · rw [hu]
        exact S.gap_point_ne_other_gap haj.symm i u
      · rw [hu]
        exact S.gap_point_ne_fork (S.step a) j i
    have hrow :
        (S.gap j).idx i ≠ (S.gap a).idx t ∧
        (S.gap j).idx i ≠ next ((S.gap a).idx t) ∧
        (∀ z, back ((S.gap a).idx t) = some z → (S.gap j).idx i ≠ z) :=
      ⟨S.gap_point_ne_other_gap haj.symm i t, hrowNext,
        fun z hz => False.elim (hbackNone z hz)⟩
    have hnext :
        next ((S.gap j).idx i) ≠ (S.gap a).idx t ∧
        next ((S.gap j).idx i) ≠ next ((S.gap a).idx t) ∧
        (∀ z, back ((S.gap a).idx t) = some z →
          next ((S.gap j).idx i) ≠ z) := by
      rcases S.next_gap_point_cases j i with ⟨u, hu⟩ | hu
      · rw [hu]
        refine ⟨S.gap_point_ne_other_gap haj.symm u t, ?_,
          fun z hz => False.elim (hbackNone z hz)⟩
        rcases S.next_gap_point_cases a t with ⟨v, hv⟩ | hv
        · rw [hv]
          exact S.gap_point_ne_other_gap haj.symm u v
        · rw [hv]
          exact S.gap_point_ne_fork (S.step a) j u
      · rw [hu]
        refine ⟨S.fork_ne_gap (S.step j) a t, ?_,
          fun z hz => False.elim (hbackNone z hz)⟩
        rcases S.next_gap_point_cases a t with ⟨v, hv⟩ | hv
        · rw [hv]
          exact S.fork_ne_gap (S.step j) a v
        · rw [hv]
          intro h
          have hs : S.step j = S.step a := S.fork.injective h
          exact haj (S.step.injective hs.symm)
    exact ⟨hrow, hnext⟩

/-- On every long gap in the paper-shaped cyclic partition, the two literal
adjacent-fork responses exist and reconstruct all internal coordinates of a
global source-current kernel vector.  Thus global kernel exclusion reduces
entirely to the fork coordinates. -/
theorem exists_literal_responses_and_reconstructs_gap
    (S : SourceCyclicNonemptyGapSystem next back) (j : Fin l)
    (hm : 0 < S.gapLength j)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (hunit : weight ((S.gap j).idx (Fin.last (S.gapLength j))) = 1)
    (x : Fin n → ℝ)
    (hker : ∀ r, ∑ k,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e r k * x k = 0) :
    ∃ xf yw : Fin (S.gapLength j + 1) → ℝ,
      (∀ i, ∑ k,
        (S.gap j).restrictedCurrentMatrix weight p q e rho i k * xf k =
          currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
              ((S.gap j).idx i) (S.fork (S.step j))) ∧
      (∀ i, ∑ k,
        (S.gap j).restrictedCurrentMatrix weight p q e rho i k * yw k =
          currentSecantKernelMatrixWith
            (orderedMonomialSecantMatrix
              (sourceProductExponent next weight back) rho)
            (sourceStoich next weight back) p q e
              ((S.gap j).idx i) (S.fork j)) ∧
      ∀ i, x ((S.gap j).idx i) =
        -(yw i * x (S.fork j) + xf i * x (S.fork (S.step j))) := by
  let G := S.gap j
  let P := S.wrap j
  obtain ⟨xf, hxf⟩ := G.restricted_response_exists weight p q e rho
    hp hq he hrho hw
    (sourceWrapForwardForcing (G.gapA p e) (G.gapC weight q e rho))
  obtain ⟨yw, hyw⟩ := G.restricted_response_exists weight p q e rho
    hp hq he hrho hw
    (sourceWrapLeftForcing (G.gapA p e) (weight (S.fork j)))
  have hrec :=
    SourceWrapGlobalColumnClosed.internal_coordinates_eq_negative_responses_of_kernel
      (S.globalColumnClosed j) hm weight p q e rho hp hq he hrho hw hunit
        x xf yw hxf hyw hker
  refine ⟨xf, yw, ?_, ?_, hrec⟩
  · intro i
    rw [P.internal_right_column_eq_forcing (by omega) weight p q e rho hunit i]
    exact hxf i
  · intro i
    rw [P.internal_left_column_eq_forcing weight p q e rho i]
    exact hyw i

/-- If all fork coordinates of a global kernel vector vanish, every gap row
has zero boundary forcing.  The killed-path block then has trivial kernel.
This argument is uniform in the gap length and in particular includes the
singleton case `gapLength = 0`. -/
theorem kernel_eq_zero_of_fork_coordinates_eq_zero
    (S : SourceCyclicNonemptyGapSystem next back)
    (weight : Fin n → ℕ) (p q e rho : Fin n → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hq : ∀ r, 0 ≤ q r)
    (he : ∀ r, 0 < e r) (hrho : ∀ r, 0 < rho r)
    (hw : ∀ r, 0 < weight r)
    (x : Fin n → ℝ)
    (hker : ∀ r, ∑ k,
      currentSecantKernelMatrixWith
          (orderedMonomialSecantMatrix
            (sourceProductExponent next weight back) rho)
          (sourceStoich next weight back) p q e r k * x k = 0)
    (hfork : ∀ j : Fin l, x (S.fork j) = 0) :
    x = 0 := by
  funext k
  change x k = 0
  rcases S.cover k with ⟨j, rfl⟩ | ⟨j, i, rfl⟩
  · exact hfork j
  · let G := S.gap j
    have hsplit := (S.globalColumnClosed j).kernel_row_split
      weight p q e rho x hker
    have hgapKernel : ∀ r,
        ∑ t, G.restrictedCurrentMatrix weight p q e rho r t * x (G.idx t) = 0 := by
      intro r
      have hr := hsplit r
      rw [hfork j, hfork (S.step j)] at hr
      simpa [G] using hr
    have hz := G.restrictedCurrentMatrix_kernel_eq_zero
      weight p q e rho hp hq he hrho hw (fun t => x (G.idx t)) hgapKernel
    exact hz i

end SourceCyclicNonemptyGapSystem

end TypeIIL

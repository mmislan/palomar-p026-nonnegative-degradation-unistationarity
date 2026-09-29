module

public import proofs.TypeIIL.SourcePathSupersolution
public import proofs.TypeIIL.SourceCorrectionBlock

@[expose] public section

namespace TypeIIL

open scoped BigOperators

def finitePathPrev {m : ℕ} (i : Fin (m + 1)) (h : 0 < i.val) : Fin (m + 1) :=
  ⟨i.val - 1, Nat.lt_trans (Nat.sub_lt h Nat.zero_lt_one) i.isLt⟩

def finitePathNext {m : ℕ} (i : Fin (m + 1)) (h : i.val < m) : Fin (m + 1) :=
  ⟨i.val + 1, Nat.succ_lt_succ h⟩

/-- The literal internal block exposed by the source-current entry ledger.
`A` is the source response, `c` the successor secant response, and `s` the
cycle multiplicity on the outgoing edge. -/
def finiteSourcePathMatrix {m : ℕ}
    (A c s : Fin (m + 1) → ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j =>
    (if j = i then 1 + A i + c i * s i else 0) +
      (if h : 0 < i.val then
        if j = finitePathPrev i h then -(A i * s (finitePathPrev i h)) else 0
      else 0) +
      (if h : i.val < m then
        if j = finitePathNext i h then -c i else 0
      else 0)

/-- Cumulative stoichiometric scaling along a finite source path. -/
def finiteSourcePathWeight {m : ℕ}
    (s : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : ℝ :=
  (Finset.Iio i).prod s

theorem finiteSourcePathWeight_pos {m : ℕ}
    {s : Fin (m + 1) → ℝ} (hs : ∀ i, 0 < s i) :
    ∀ i, 0 < finiteSourcePathWeight s i := by
  intro i
  exact Finset.prod_pos fun j _ => hs j

theorem finiteSourcePathWeight_one_le {m : ℕ}
    {s : Fin (m + 1) → ℝ} (hs : ∀ i, 1 ≤ s i) :
    ∀ i, 1 ≤ finiteSourcePathWeight s i := by
  intro i
  exact Finset.one_le_prod₀ fun j _ => hs j

theorem finiteSourcePathWeight_next {m : ℕ}
    (s : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (h : i.val < m) :
    finiteSourcePathWeight s (finitePathNext i h) =
      s i * finiteSourcePathWeight s i := by
  have hIio : Finset.Iio (finitePathNext i h) =
      insert i (Finset.Iio i) := by
    ext j
    simp only [Finset.mem_Iio, Finset.mem_insert]
    constructor
    · intro hj
      change j.val < i.val + 1 at hj
      have hle : j.val ≤ i.val := by omega
      rcases lt_or_eq_of_le hle with hlt | heq
      · right
        exact hlt
      · left
        exact Fin.ext heq
    · intro hj
      rcases hj with hji | hj
      · subst j
        change i.val < i.val + 1
        omega
      · change j.val < i.val at hj
        change j.val < i.val + 1
        omega
  rw [finiteSourcePathWeight, finiteSourcePathWeight, hIio]
  rw [Finset.prod_insert (by simp)]

theorem finiteSourcePathWeight_prev {m : ℕ}
    (s : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (h : 0 < i.val) :
    finiteSourcePathWeight s i =
      s (finitePathPrev i h) *
        finiteSourcePathWeight s (finitePathPrev i h) := by
  have hpnext : finitePathNext (finitePathPrev i h) (by
      dsimp [finitePathPrev]
      omega) = i := by
    apply Fin.ext
    dsimp [finitePathNext, finitePathPrev]
    omega
  simpa [hpnext] using finiteSourcePathWeight_next s (finitePathPrev i h) (by
    dsimp [finitePathPrev]
    omega)

/-- Direct row expansion against an arbitrary vector. -/
theorem finiteSourcePathMatrix_mul_apply {m : ℕ}
    (A c s x : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    ∑ j, finiteSourcePathMatrix A c s i j * x j =
      (1 + A i + c i * s i) * x i +
        (if h : 0 < i.val then
          -(A i * s (finitePathPrev i h)) * x (finitePathPrev i h)
        else 0) +
        (if h : i.val < m then
          (-c i) * x (finitePathNext i h)
        else 0) := by
  classical
  unfold finiteSourcePathMatrix
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp
  ring

/-- Direct row expansion, retaining the two cut indicators. -/
theorem finiteSourcePathMatrix_mul_weight {m : ℕ}
    (A c s : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    ∑ j, finiteSourcePathMatrix A c s i j * finiteSourcePathWeight s j =
      (1 + A i + c i * s i) * finiteSourcePathWeight s i +
        (if h : 0 < i.val then
          -(A i * s (finitePathPrev i h)) *
            finiteSourcePathWeight s (finitePathPrev i h)
        else 0) +
        (if h : i.val < m then
          (-c i) * finiteSourcePathWeight s (finitePathNext i h)
        else 0) :=
  finiteSourcePathMatrix_mul_apply A c s (finiteSourcePathWeight s) i

/-- Exact cumulative-weight residual.  Interior transport cancels, leaving
the identity margin in every row and one additional gain at each cut
boundary. -/
theorem finiteSourcePathMatrix_mul_weight_exact_boundary {m : ℕ}
    (A c s : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    ∑ j, finiteSourcePathMatrix A c s i j * finiteSourcePathWeight s j =
      finiteSourcePathWeight s i +
        (if i.val = 0 then A i * finiteSourcePathWeight s i else 0) +
        (if i.val = m then
          c i * s i * finiteSourcePathWeight s i else 0) := by
  rw [finiteSourcePathMatrix_mul_weight]
  by_cases hp : 0 < i.val
  · rw [dite_eq_left hp]
    by_cases hn : i.val < m
    · rw [dite_eq_left hn, finiteSourcePathWeight_next s i hn,
          finiteSourcePathWeight_prev s i hp]
      have hi0 : i.val ≠ 0 := by omega
      have him : i.val ≠ m := by omega
      simp [hi0, him]
      ring
    · rw [dite_eq_right hn]
      rw [finiteSourcePathWeight_prev s i hp]
      have hi0 : i.val ≠ 0 := by omega
      have him : i.val = m := by omega
      have hm0 : m ≠ 0 := by omega
      simp [him, hm0]
      ring
  · rw [dite_eq_right hp]
    have hi0 : i.val = 0 := by omega
    by_cases hn : i.val < m
    · rw [dite_eq_left hn, finiteSourcePathWeight_next s i hn]
      have hm0 : 0 ≠ m := by omega
      simp [hi0, hm0]
      ring
    · rw [dite_eq_right hn]
      have him : i.val = m := by omega
      have hm0 : m = 0 := by omega
      simp [hi0, hm0]
      ring

def finiteSourcePathBoundaryForcing {m : ℕ}
    (A c : Fin (m + 1) → ℝ) (scale : ℝ) : Fin (m + 1) → ℝ :=
  fun i =>
    (if i.val = 0 then A i * scale else 0) +
      (if i.val = m then c i else 0)

/-- The physical forcing from the two adjacent forks is bounded by the
scaled cumulative supersolution.  This is the inverse-free attenuation
estimate for an arbitrary weighted source gap. -/
theorem finiteSourcePathBoundaryForcing_le_mul_weight {m : ℕ}
    {A c s : Fin (m + 1) → ℝ} {scale : ℝ}
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 1 ≤ s i) (hscale : 1 ≤ scale) :
    ∀ i, finiteSourcePathBoundaryForcing A c scale i ≤
      ∑ j, finiteSourcePathMatrix A c s i j *
        (scale * finiteSourcePathWeight s j) := by
  intro i
  have hweight := finiteSourcePathWeight_one_le hs i
  have hscale0 : 0 ≤ scale := le_trans zero_le_one hscale
  have hweight0 : 0 ≤ finiteSourcePathWeight s i :=
    le_trans zero_le_one hweight
  have hbase : 0 ≤ scale * finiteSourcePathWeight s i :=
    mul_nonneg hscale0 hweight0
  have hfirst :
      (if i.val = 0 then A i * scale else 0) ≤
        scale * (if i.val = 0 then
          A i * finiteSourcePathWeight s i else 0) := by
    by_cases hi : i.val = 0
    · rw [ite_eq_left hi, ite_eq_left hi]
      have hmul : A i * scale ≤
          (A i * scale) * finiteSourcePathWeight s i :=
        by simpa using
          mul_le_mul_of_nonneg_left hweight (mul_nonneg (hA i) hscale0)
      nlinarith
    · simp [hi]
  have hlast :
      (if i.val = m then c i else 0) ≤
        scale * (if i.val = m then
          c i * s i * finiteSourcePathWeight s i else 0) := by
    by_cases hi : i.val = m
    · rw [ite_eq_left hi, ite_eq_left hi]
      have hs0 : 0 ≤ s i := le_trans zero_le_one (hs i)
      have hsw : 1 ≤ scale * (s i * finiteSourcePathWeight s i) := by
        have h₁ : 1 ≤ s i * finiteSourcePathWeight s i :=
          one_le_mul_of_one_le_of_one_le (hs i) hweight
        exact one_le_mul_of_one_le_of_one_le hscale h₁
      have hmul : c i ≤ c i *
          (scale * (s i * finiteSourcePathWeight s i)) :=
        by simpa using mul_le_mul_of_nonneg_left hsw (hc i)
      nlinarith
    · simp [hi]
  rw [finiteSourcePathBoundaryForcing]
  have hsum := add_le_add hfirst hlast
  have hfactor :
      (∑ j, finiteSourcePathMatrix A c s i j *
          (scale * finiteSourcePathWeight s j)) =
        scale * (∑ j, finiteSourcePathMatrix A c s i j *
          finiteSourcePathWeight s j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfactor, finiteSourcePathMatrix_mul_weight_exact_boundary]
  nlinarith

theorem finiteSourcePathMatrix_offdiag_nonpos {m : ℕ}
    {A c s : Fin (m + 1) → ℝ}
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 0 ≤ s i) :
    ∀ i j, i ≠ j → finiteSourcePathMatrix A c s i j ≤ 0 := by
  intro i j hij
  have hprev :
      (if h : 0 < i.val then
        if j = finitePathPrev i h then -(A i * s (finitePathPrev i h)) else 0
      else 0) ≤ 0 := by
    by_cases hp : 0 < i.val
    · rw [dite_eq_left hp]
      by_cases hjp : j = finitePathPrev i hp
      · rw [ite_eq_left hjp]
        exact neg_nonpos.mpr (mul_nonneg (hA i) (hs _))
      · rw [ite_eq_right hjp]
    · rw [dite_eq_right hp]
  have hnext :
      (if h : i.val < m then
        if j = finitePathNext i h then -c i else 0
      else 0) ≤ 0 := by
    by_cases hn : i.val < m
    · rw [dite_eq_left hn]
      by_cases hjn : j = finitePathNext i hn
      · rw [ite_eq_left hjn]
        exact neg_nonpos.mpr (hc i)
      · rw [ite_eq_right hjn]
    · rw [dite_eq_right hn]
  unfold finiteSourcePathMatrix
  rw [ite_eq_right (Ne.symm hij)]
  linarith

/-- The cumulative vector is a strict supersolution for every finite weighted
source path.  Interior transport cancels exactly; either missing boundary
term only increases the margin. -/
theorem finiteSourcePathMatrix_mul_weight_pos {m : ℕ}
    {A c s : Fin (m + 1) → ℝ}
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 0 < s i) :
    ∀ i, 0 < ∑ j,
      finiteSourcePathMatrix A c s i j * finiteSourcePathWeight s j := by
  intro i
  rw [finiteSourcePathMatrix_mul_weight]
  by_cases hp : 0 < i.val
  · rw [dite_eq_left hp]
    by_cases hn : i.val < m
    · rw [dite_eq_left hn]
      simpa [sub_eq_add_neg] using source_path_interior_scaling_pos
        (A := A i) (c := c i)
        (sPrev := s (finitePathPrev i hp)) (sNext := s i)
        (finiteSourcePathWeight_pos hs i)
        (finiteSourcePathWeight_prev s i hp)
        (finiteSourcePathWeight_next s i hn)
    · rw [dite_eq_right hn]
      simpa [sub_eq_add_neg] using source_path_right_scaling_pos
        (A := A i) (c := c i)
        (sPrev := s (finitePathPrev i hp)) (sNext := s i)
        (hc i) (le_of_lt (hs i)) (finiteSourcePathWeight_pos hs i)
        (finiteSourcePathWeight_prev s i hp)
  · rw [dite_eq_right hp]
    by_cases hn : i.val < m
    · rw [dite_eq_left hn]
      simpa [sub_eq_add_neg] using source_path_left_scaling_pos
        (A := A i) (c := c i) (sNext := s i)
        (hA i) (finiteSourcePathWeight_pos hs i)
        (finiteSourcePathWeight_next s i hn)
    · rw [dite_eq_right hn]
      simpa using source_path_singleton_scaling_pos
        (A := A i) (c := c i) (sNext := s i)
        (hA i) (hc i) (le_of_lt (hs i))
        (finiteSourcePathWeight_pos hs i)

/-- Every finite literal source path block has trivial kernel. -/
theorem finiteSourcePathMatrix_kernel_eq_zero {m : ℕ}
    {A c s : Fin (m + 1) → ℝ}
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 0 < s i)
    (x : Fin (m + 1) → ℝ)
    (hker : ∀ i, ∑ j, finiteSourcePathMatrix A c s i j * x j = 0) :
    ∀ i, x i = 0 := by
  apply zmatrix_kernel_eq_zero (finiteSourcePathMatrix A c s)
    (finiteSourcePathWeight s) x
  · exact finiteSourcePathMatrix_offdiag_nonpos hA hc
      (fun i => le_of_lt (hs i))
  · exact finiteSourcePathWeight_pos hs
  · exact finiteSourcePathMatrix_mul_weight_pos hA hc hs
  · exact hker

/-- Nonnegative endpoint forcing produces a nonnegative response throughout
the finite source path. -/
theorem finiteSourcePathBoundaryResponse_nonneg {m : ℕ}
    {A c s y : Fin (m + 1) → ℝ} {scale : ℝ}
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 0 < s i) (hscale : 0 ≤ scale)
    (hsolve : ∀ i,
      ∑ j, finiteSourcePathMatrix A c s i j * y j =
        finiteSourcePathBoundaryForcing A c scale i) :
    ∀ i, 0 ≤ y i := by
  apply zmatrix_solution_nonneg
    (finiteSourcePathMatrix A c s) (finiteSourcePathWeight s) y
    (finiteSourcePathBoundaryForcing A c scale)
  · exact finiteSourcePathMatrix_offdiag_nonpos hA hc
      (fun i => le_of_lt (hs i))
  · exact finiteSourcePathWeight_pos hs
  · exact finiteSourcePathMatrix_mul_weight_pos hA hc hs
  · intro i
    unfold finiteSourcePathBoundaryForcing
    have hAs : 0 ≤ A i * scale := mul_nonneg (hA i) hscale
    have hci : 0 ≤ c i := hc i
    split_ifs <;> linarith
  · exact hsolve

/-- A boundary response of a finite weighted source path is dominated by the
scaled cumulative path weight.  This packages the strict `Z`-matrix Green
comparison without introducing an inverse. -/
theorem finiteSourcePathBoundaryResponse_le_weight {m : ℕ}
    {A c s y : Fin (m + 1) → ℝ} {scale : ℝ}
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 1 ≤ s i) (hscale : 1 ≤ scale)
    (hsolve : ∀ i,
      ∑ j, finiteSourcePathMatrix A c s i j * y j =
        finiteSourcePathBoundaryForcing A c scale i) :
    ∀ i, y i ≤ scale * finiteSourcePathWeight s i := by
  apply zmatrix_solution_le_supersolution
    (finiteSourcePathMatrix A c s)
    (fun i => scale * finiteSourcePathWeight s i) y
    (finiteSourcePathBoundaryForcing A c scale)
  · exact finiteSourcePathMatrix_offdiag_nonpos hA hc
      (fun i => le_trans zero_le_one (hs i))
  · intro i
    exact mul_pos (lt_of_lt_of_le zero_lt_one hscale)
      (finiteSourcePathWeight_pos
        (fun j => lt_of_lt_of_le zero_lt_one (hs j)) i)
  · intro i
    have hfactor :
        (∑ j, finiteSourcePathMatrix A c s i j *
            (scale * finiteSourcePathWeight s j)) =
          scale * (∑ j, finiteSourcePathMatrix A c s i j *
            finiteSourcePathWeight s j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hfactor]
    exact mul_pos (lt_of_lt_of_le zero_lt_one hscale)
      (finiteSourcePathMatrix_mul_weight_pos hA hc
        (fun j => lt_of_lt_of_le zero_lt_one (hs j)) i)
  · exact hsolve
  · exact finiteSourcePathBoundaryForcing_le_mul_weight hA hc hs hscale

/-- Exact terminal Green correction for an arbitrary nonempty weighted source
path.  The final row supplies the mixed boundary inequality needed by the
adjacent fork after internal elimination. -/
theorem finiteSourcePath_terminal_mixed_boundary_nonpos
    {m : ℕ} (hm : 0 < m)
    {A c s y b : Fin (m + 1) → ℝ} {h g t : ℝ}
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 0 < s i) (hAlast : 0 < A (Fin.last m))
    (hb : ∀ i, 0 ≤ b i)
    (hsolve : ∀ i, ∑ j, finiteSourcePathMatrix A c s i j * y j = b i)
    (hh : 0 ≤ h) (ht : 0 ≤ t)
    (htransport :
      h * t * (1 + A (Fin.last m) + c (Fin.last m) * s (Fin.last m)) ≤
        (g + h) *
          (A (Fin.last m) *
            s (finitePathPrev (Fin.last m) (by simpa using hm)))) :
    h * t * y (finitePathPrev (Fin.last m) (by simpa using hm)) -
        (g + h) * y (Fin.last m) ≤ 0 := by
  let last : Fin (m + 1) := Fin.last m
  have hlastpos : 0 < last.val := by
    simpa [last] using hm
  let prev : Fin (m + 1) := finitePathPrev last hlastpos
  let a := A last * s prev
  let d := 1 + A last + c last * s last
  have ha : 0 < a := mul_pos (by simpa [last] using hAlast) (hs prev)
  have hterminal : d * y last - a * y prev = b last := by
    have hrow := hsolve last
    rw [finiteSourcePathMatrix_mul_apply] at hrow
    have hn : ¬ last.val < m := by
      simp [last]
    rw [dite_eq_left hlastpos, dite_eq_right hn] at hrow
    simpa [a, d, prev, sub_eq_add_neg] using hrow
  apply zmatrix_terminal_mixed_boundary_nonpos
    (finiteSourcePathMatrix A c s) (finiteSourcePathWeight s) y b prev last
  · exact finiteSourcePathMatrix_offdiag_nonpos hA hc
      (fun i => le_of_lt (hs i))
  · exact finiteSourcePathWeight_pos hs
  · exact finiteSourcePathMatrix_mul_weight_pos hA hc hs
  · exact hb
  · exact hsolve
  · exact ha
  · exact hh
  · exact ht
  · exact hterminal
  · simpa [a, d, last, prev] using htransport

end TypeIIL

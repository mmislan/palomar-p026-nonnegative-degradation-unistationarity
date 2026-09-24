import proofs.TypeII3.Network.QuotientAllZero

namespace MixedDegradation.Coincident
open TypeII3

/- The same literal three-fork reactions as the source quotient, but with
nonnegative loss in the model itself. Old positive-loss rate records are
deliberately not used at this public boundary. -/
structure AllZeroParams where
  plus0 : ℝ
  plus1 : ℝ
  plus2 : ℝ
  minus0 : ℝ
  minus1 : ℝ
  minus2 : ℝ
  d0 : ℝ
  d1 : ℝ
  d2 : ℝ
  m0 : ℕ
  m1 : ℕ
  m2 : ℕ
  plus0_pos : 0 < plus0
  plus1_pos : 0 < plus1
  plus2_pos : 0 < plus2
  minus0_pos : 0 < minus0
  minus1_pos : 0 < minus1
  minus2_pos : 0 < minus2
  d0_nonneg : 0 ≤ d0
  d1_nonneg : 0 ≤ d1
  d2_nonneg : 0 ≤ d2
  m0_pos : 0 < m0
  m1_pos : 0 < m1
  m2_pos : 0 < m2

@[ext] structure AllZeroState where
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ

def PositiveAllZeroState (x : AllZeroState) : Prop :=
  0 < x.x0 ∧ 0 < x.x1 ∧ 0 < x.x2

def allZeroCurrent0 (p : AllZeroParams) (x : AllZeroState) : ℝ :=
  p.plus0 * x.x0 - p.minus0 * x.x1 ^ p.m0 * x.x2

def allZeroCurrent1 (p : AllZeroParams) (x : AllZeroState) : ℝ :=
  p.plus1 * x.x1 - p.minus1 * x.x2 ^ p.m1 * x.x0

def allZeroCurrent2 (p : AllZeroParams) (x : AllZeroState) : ℝ :=
  p.plus2 * x.x2 - p.minus2 * x.x0 ^ p.m2 * x.x1

def IsAllZeroStationary (p : AllZeroParams) (x : AllZeroState) : Prop :=
  -allZeroCurrent0 p x + allZeroCurrent1 p x +
      p.m2 * allZeroCurrent2 p x - p.d0 * x.x0 = 0 ∧
  p.m0 * allZeroCurrent0 p x - allZeroCurrent1 p x +
      allZeroCurrent2 p x - p.d1 * x.x1 = 0 ∧
  allZeroCurrent0 p x + p.m1 * allZeroCurrent1 p x -
      allZeroCurrent2 p x - p.d2 * x.x2 = 0


theorem nonnegative_weighted_cross
    {Delta A B d e c u v : ℝ}
    (hDelta : 0 < Delta) (hA : 0 < A) (hB : 0 < B)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcross : Delta * c = A * d * u + B * e * v) : 0 ≤ c := by
  have h : 0 ≤ Delta * c := by
    rw [hcross]
    exact add_nonneg (mul_nonneg (mul_nonneg hA.le hd) hu)
      (mul_nonneg (mul_nonneg hB.le he) hv)
  exact nonneg_of_mul_nonneg_right h hDelta

theorem nonpositive_weighted_cross
    {Delta A B d e c u v : ℝ}
    (hDelta : 0 < Delta) (hA : 0 < A) (hB : 0 < B)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hu : u ≤ 0) (hv : v ≤ 0)
    (hcross : Delta * c = A * d * u + B * e * v) : c ≤ 0 := by
  have h : Delta * c ≤ 0 := by
    rw [hcross]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hA.le hd) hu)
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hB.le he) hv)
  exact nonpos_of_mul_nonpos_right h hDelta

/-- At most one positive stationary state for the coincident three-fork
literal model, arbitrary positive integer fork weights and nonnegative losses. -/
theorem all_zero_unistationarity
    (p : AllZeroParams) (x y : AllZeroState)
    (hx : PositiveAllZeroState x) (hy : PositiveAllZeroState y)
    (hxstat : IsAllZeroStationary p x)
    (hystat : IsAllZeroStationary p y) : x = y := by
  rcases hx with ⟨hx0, hx1, hx2⟩
  rcases hy with ⟨hy0, hy1, hy2⟩
  simp only [IsAllZeroStationary] at hxstat hystat
  rcases hxstat with ⟨hxB0, hxB1, hxB2⟩
  rcases hystat with ⟨hyB0, hyB1, hyB2⟩
  let qx0 := allZeroCurrent0 p x
  let qx1 := allZeroCurrent1 p x
  let qx2 := allZeroCurrent2 p x
  let qy0 := allZeroCurrent0 p y
  let qy1 := allZeroCurrent1 p y
  let qy2 := allZeroCurrent2 p y
  change -qx0 + qx1 + p.m2 * qx2 - p.d0 * x.x0 = 0 at hxB0
  change p.m0 * qx0 - qx1 + qx2 - p.d1 * x.x1 = 0 at hxB1
  change qx0 + p.m1 * qx1 - qx2 - p.d2 * x.x2 = 0 at hxB2
  change -qy0 + qy1 + p.m2 * qy2 - p.d0 * y.x0 = 0 at hyB0
  change p.m0 * qy0 - qy1 + qy2 - p.d1 * y.x1 = 0 at hyB1
  change qy0 + p.m1 * qy1 - qy2 - p.d2 * y.x2 = 0 at hyB2
  let Delta : ℝ := p.m0 + p.m1 + p.m2 + p.m0 * p.m1 * p.m2
  have hDelta : 0 < Delta := by
    dsimp [Delta]
    have hm0 : (0 : ℝ) < p.m0 := by exact_mod_cast p.m0_pos
    positivity
  have ix0 := allZeroCurrent0_inverse hxB0 hxB1 hxB2
  have iy0 := allZeroCurrent0_inverse hyB0 hyB1 hyB2
  have ix1 := allZeroCurrent1_inverse hxB0 hxB1 hxB2
  have iy1 := allZeroCurrent1_inverse hyB0 hyB1 hyB2
  have ix2 := allZeroCurrent2_inverse hxB0 hxB1 hxB2
  have iy2 := allZeroCurrent2_inverse hyB0 hyB1 hyB2
  change Delta * qx0 = _ at ix0
  change Delta * qy0 = _ at iy0
  change Delta * qx1 = _ at ix1
  change Delta * qy1 = _ at iy1
  change Delta * qx2 = _ at ix2
  change Delta * qy2 = _ at iy2
  have cross0 : Delta * (x.x0 * qy0 - y.x0 * qx0) =
      (1 + p.m1 * p.m2) * p.d1 * (x.x0 * y.x1 - y.x0 * x.x1) +
      (1 + p.m2) * p.d2 * (x.x0 * y.x2 - y.x0 * x.x2) := by
    calc
      Delta * (x.x0 * qy0 - y.x0 * qx0) =
          x.x0 * (Delta * qy0) - y.x0 * (Delta * qx0) := by ring
      _ = _ := by rw [ix0, iy0]; ring
  have cross1 : Delta * (x.x1 * qy1 - y.x1 * qx1) =
      (1 + p.m0) * p.d0 * (x.x1 * y.x0 - y.x1 * x.x0) +
      (1 + p.m0 * p.m2) * p.d2 * (x.x1 * y.x2 - y.x1 * x.x2) := by
    calc
      Delta * (x.x1 * qy1 - y.x1 * qx1) =
          x.x1 * (Delta * qy1) - y.x1 * (Delta * qx1) := by ring
      _ = _ := by rw [ix1, iy1]; ring
  have cross2 : Delta * (x.x2 * qy2 - y.x2 * qx2) =
      (1 + p.m0 * p.m1) * p.d0 * (x.x2 * y.x0 - y.x2 * x.x0) +
      (1 + p.m1) * p.d1 * (x.x2 * y.x1 - y.x2 * x.x1) := by
    calc
      Delta * (x.x2 * qy2 - y.x2 * qx2) =
          x.x2 * (Delta * qy2) - y.x2 * (Delta * qx2) := by ring
      _ = _ := by rw [ix2, iy2]; ring
  let z0 := x.x0 / y.x0
  let z1 := x.x1 / y.x1
  let z2 := x.x2 / y.x2
  have hz0 : 0 < z0 := div_pos hx0 hy0
  have hz1 : 0 < z1 := div_pos hx1 hy1
  have hz2 : 0 < z2 := div_pos hx2 hy2
  by_contra hxy
  have hzne : ¬ (z0 = z1 ∧ z1 = z2) := by
    intro hz
    have hx0z : x.x0 = z0 * y.x0 := eq_mul_of_div_eq hy0 (by rfl)
    have hx1z : x.x1 = z0 * y.x1 := eq_mul_of_div_eq hy1 (by
      change z1 = z0
      exact hz.1.symm)
    have hx2z : x.x2 = z0 * y.x2 := eq_mul_of_div_eq hy2 (by
      change z2 = z0
      exact hz.2.symm.trans hz.1.symm)
    have hc01 : x.x0 * y.x1 - y.x0 * x.x1 = 0 := by rw [hx0z, hx1z]; ring
    have hc02 : x.x0 * y.x2 - y.x0 * x.x2 = 0 := by rw [hx0z, hx2z]; ring
    have hqcross : x.x0 * qy0 - y.x0 * qx0 = 0 := by
      have hzprod : Delta * (x.x0 * qy0 - y.x0 * qx0) = 0 := by
        rw [cross0, hc01, hc02]
        ring
      exact (mul_eq_zero.mp hzprod).resolve_left (ne_of_gt hDelta)
    have hk : x.x0 * qy0 - y.x0 * qx0 =
        p.minus0 * (y.x0 * x.x1 ^ p.m0 * x.x2 -
          x.x0 * y.x1 ^ p.m0 * y.x2) := by
      apply fork_cross_eq
      · rfl
      · rfl
    have hraw : y.x0 * x.x1 ^ p.m0 * x.x2 -
        x.x0 * y.x1 ^ p.m0 * y.x2 = 0 := by
      rw [hqcross] at hk
      exact (mul_eq_zero.mp hk.symm).resolve_left (ne_of_gt p.minus0_pos)
    rw [hx0z, hx1z, hx2z] at hraw
    have hz_one := positive_scale_fork_forces_one hz0 hy0 hy1 hy2 p.m0_pos hraw
    apply hxy
    apply AllZeroState.ext
    · rw [hx0z, hz_one, one_mul]
    · rw [hx1z, hz_one, one_mul]
    · rw [hx2z, hz_one, one_mul]
  rcases ratio_bad_extremum hz0 hz1 hz2 p.m0_pos p.m1_pos p.m2_pos hzne with
    h | h | h | h | h | h
  all_goals
    dsimp [z0, z1, z2] at h
  · have c1 := ratio_le_cross_nonneg hy1 hy0 h.1
    have c2 := ratio_le_cross_nonneg hy2 hy0 h.2.1
    have cp := nonnegative_weighted_cross hDelta (by positivity) (by positivity)
      p.d1_nonneg p.d2_nonneg c1 c2 cross0
    have raw := ratio_product_lt_raw hy1 hy2 hy0 h.2.2
    have k := fork_cross_eq (qx := qx0) (qy := qy0)
      (by rfl) (by rfl)
    have ck : x.x0 * qy0 - y.x0 * qx0 < 0 := k.trans_lt
      (mul_neg_of_pos_of_neg p.minus0_pos (sub_neg.mpr raw))
    exact (not_lt_of_ge cp) ck
  · have c1 := ratio_le_cross_nonneg hy0 hy1 h.1
    have c2 := ratio_le_cross_nonneg hy2 hy1 h.2.1
    have cp := nonnegative_weighted_cross hDelta (by positivity) (by positivity)
      p.d0_nonneg p.d2_nonneg c1 c2 cross1
    have raw := ratio_product_lt_raw hy2 hy0 hy1 h.2.2
    have k := fork_cross_eq (qx := qx1) (qy := qy1)
      (by rfl) (by rfl)
    have ck : x.x1 * qy1 - y.x1 * qx1 < 0 := k.trans_lt
      (mul_neg_of_pos_of_neg p.minus1_pos (sub_neg.mpr raw))
    exact (not_lt_of_ge cp) ck
  · have c1 := ratio_le_cross_nonneg hy0 hy2 h.1
    have c2 := ratio_le_cross_nonneg hy1 hy2 h.2.1
    have cp := nonnegative_weighted_cross hDelta (by positivity) (by positivity)
      p.d0_nonneg p.d1_nonneg c1 c2 cross2
    have raw := ratio_product_lt_raw hy0 hy1 hy2 h.2.2
    have k := fork_cross_eq (qx := qx2) (qy := qy2)
      (by rfl) (by rfl)
    have ck : x.x2 * qy2 - y.x2 * qx2 < 0 := k.trans_lt
      (mul_neg_of_pos_of_neg p.minus2_pos (sub_neg.mpr raw))
    exact (not_lt_of_ge cp) ck
  · have c1 : x.x0 * y.x1 - y.x0 * x.x1 ≤ 0 := by
      have hc := ratio_le_cross_nonneg hy0 hy1 h.1
      linarith only [hc]
    have c2 : x.x0 * y.x2 - y.x0 * x.x2 ≤ 0 := by
      have hc := ratio_le_cross_nonneg hy0 hy2 h.2.1
      linarith only [hc]
    have cp := nonpositive_weighted_cross hDelta (by positivity) (by positivity)
      p.d1_nonneg p.d2_nonneg c1 c2 cross0
    have raw := ratio_product_gt_raw hy1 hy2 hy0 h.2.2
    have k := fork_cross_eq (qx := qx0) (qy := qy0)
      (by rfl) (by rfl)
    have ck : 0 < x.x0 * qy0 - y.x0 * qx0 := k.symm ▸
      mul_pos p.minus0_pos (sub_pos.mpr raw)
    exact (not_lt_of_ge cp) ck
  · have c1 : x.x1 * y.x0 - y.x1 * x.x0 ≤ 0 := by
      have hc := ratio_le_cross_nonneg hy1 hy0 h.1
      linarith only [hc]
    have c2 : x.x1 * y.x2 - y.x1 * x.x2 ≤ 0 := by
      have hc := ratio_le_cross_nonneg hy1 hy2 h.2.1
      linarith only [hc]
    have cp := nonpositive_weighted_cross hDelta (by positivity) (by positivity)
      p.d0_nonneg p.d2_nonneg c1 c2 cross1
    have raw := ratio_product_gt_raw hy2 hy0 hy1 h.2.2
    have k := fork_cross_eq (qx := qx1) (qy := qy1)
      (by rfl) (by rfl)
    have ck : 0 < x.x1 * qy1 - y.x1 * qx1 := k.symm ▸
      mul_pos p.minus1_pos (sub_pos.mpr raw)
    exact (not_lt_of_ge cp) ck
  · have c1 : x.x2 * y.x0 - y.x2 * x.x0 ≤ 0 := by
      have hc := ratio_le_cross_nonneg hy2 hy0 h.1
      linarith only [hc]
    have c2 : x.x2 * y.x1 - y.x2 * x.x1 ≤ 0 := by
      have hc := ratio_le_cross_nonneg hy2 hy1 h.2.1
      linarith only [hc]
    have cp := nonpositive_weighted_cross hDelta (by positivity) (by positivity)
      p.d0_nonneg p.d1_nonneg c1 c2 cross2
    have raw := ratio_product_gt_raw hy0 hy1 hy2 h.2.2
    have k := fork_cross_eq (qx := qx2) (qy := qy2)
      (by rfl) (by rfl)
    have ck : 0 < x.x2 * qy2 - y.x2 * qx2 := k.symm ▸
      mul_pos p.minus2_pos (sub_pos.mpr raw)
    exact (not_lt_of_ge cp) ck


end MixedDegradation.Coincident


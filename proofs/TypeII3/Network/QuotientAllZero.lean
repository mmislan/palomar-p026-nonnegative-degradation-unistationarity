import Mathlib

namespace TypeII3

theorem ordered_cycle_bad_forward
    {lo mid hi : ℝ} {m n : ℕ}
    (hlo : 0 < lo) (hlm : lo ≤ mid) (hmh : mid ≤ hi) (hlh : lo < hi)
    (hm : 0 < m) (hn : 0 < n) :
    lo ^ m * mid < hi ∨ lo < mid ^ n * hi := by
  by_contra h
  push Not at h
  rcases h with ⟨hfirst, hsecond⟩
  have hpowNonneg : 0 ≤ lo ^ m := pow_nonneg (le_of_lt hlo) m
  have hbound : lo ^ m * mid ≤ lo ^ m * hi :=
    mul_le_mul_of_nonneg_left hmh hpowNonneg
  have hhi : 0 < hi := lt_of_lt_of_le hlo (le_trans hlm hmh)
  have hp : 1 ≤ lo ^ m := by nlinarith
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hlo1 : 1 ≤ lo := (one_le_pow_iff_of_nonneg (le_of_lt hlo) hm0).mp hp
  have hmid1 : 1 ≤ mid := le_trans hlo1 hlm
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hpn : 1 ≤ mid ^ n :=
    (one_le_pow_iff_of_nonneg (le_of_lt (lt_of_lt_of_le hlo hlm)) hn0).mpr hmid1
  have hgrow : hi ≤ mid ^ n * hi := by nlinarith
  nlinarith

theorem ordered_cycle_bad_backward
    {lo mid hi : ℝ} {m n : ℕ}
    (hlo : 0 < lo) (hlm : lo ≤ mid) (hmh : mid ≤ hi) (hlh : lo < hi)
    (hm : 0 < m) (hn : 0 < n) :
    mid ^ m * lo < hi ∨ lo < hi ^ n * mid := by
  by_contra h
  push Not at h
  rcases h with ⟨hfirst, hsecond⟩
  have hmid : 0 < mid := lt_of_lt_of_le hlo hlm
  have hpowNonneg : 0 ≤ hi ^ n := pow_nonneg (le_trans (le_of_lt hlo) (le_trans hlm hmh)) n
  have hbound : hi ^ n * lo ≤ hi ^ n * mid :=
    mul_le_mul_of_nonneg_left hlm hpowNonneg
  have hp : hi ^ n ≤ 1 := by nlinarith
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hhi1 : hi ≤ 1 :=
    (pow_le_one_iff_of_nonneg (le_trans (le_of_lt hlo) (le_trans hlm hmh)) hn0).mp hp
  have hmid1 : mid ≤ 1 := le_trans hmh hhi1
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hpm : mid ^ m ≤ 1 :=
    (pow_le_one_iff_of_nonneg (le_of_lt hmid) hm0).mpr hmid1
  have hshrink : mid ^ m * lo ≤ lo := by nlinarith
  nlinarith

def BadRatioExtremum
    (z0 z1 z2 : ℝ) (m0 m1 m2 : ℕ) : Prop :=
  (z1 ≤ z0 ∧ z2 ≤ z0 ∧ z1 ^ m0 * z2 < z0) ∨
  (z0 ≤ z1 ∧ z2 ≤ z1 ∧ z2 ^ m1 * z0 < z1) ∨
  (z0 ≤ z2 ∧ z1 ≤ z2 ∧ z0 ^ m2 * z1 < z2) ∨
  (z0 ≤ z1 ∧ z0 ≤ z2 ∧ z0 < z1 ^ m0 * z2) ∨
  (z1 ≤ z0 ∧ z1 ≤ z2 ∧ z1 < z2 ^ m1 * z0) ∨
  (z2 ≤ z0 ∧ z2 ≤ z1 ∧ z2 < z0 ^ m2 * z1)

theorem ratio_bad_extremum
    {z0 z1 z2 : ℝ} {m0 m1 m2 : ℕ}
    (hz0 : 0 < z0) (hz1 : 0 < z1) (hz2 : 0 < z2)
    (hm0 : 0 < m0) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (hne : ¬ (z0 = z1 ∧ z1 = z2)) :
    BadRatioExtremum z0 z1 z2 m0 m1 m2 := by
  rcases le_total z0 z1 with h01 | h10
  · rcases le_total z1 z2 with h12 | h21
    · have h02 : z0 ≤ z2 := le_trans h01 h12
      have hlt : z0 < z2 := by
        rcases lt_or_eq_of_le h02 with h | h
        · exact h
        · exfalso
          apply hne
          constructor <;> nlinarith
      rcases ordered_cycle_bad_forward hz0 h01 h12 hlt hm2 hm0 with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨h02, h12, h⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h01, h02, h⟩)))
    · rcases le_total z0 z2 with h02 | h20
      · have hlt : z0 < z1 := by
          rcases lt_or_eq_of_le h01 with h | h
          · exact h
          · exfalso
            apply hne
            constructor <;> nlinarith
        rcases ordered_cycle_bad_backward hz0 h02 h21 hlt hm1 hm0 with h | h
        · exact Or.inr (Or.inl ⟨h01, h21, h⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h01, h02, h⟩)))
      · have hlt : z2 < z1 := by
          rcases lt_or_eq_of_le h21 with h | h
          · exact h
          · exfalso
            apply hne
            constructor <;> nlinarith
        rcases ordered_cycle_bad_forward hz2 h20 h01 hlt hm1 hm2 with h | h
        · exact Or.inr (Or.inl ⟨h01, h21, h⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h20, h21, h⟩))))
  · rcases le_total z0 z2 with h02 | h20
    · have hlt : z1 < z2 := by
        rcases lt_or_eq_of_le (le_trans h10 h02) with h | h
        · exact h
        · exfalso
          apply hne
          constructor <;> nlinarith
      rcases ordered_cycle_bad_backward hz1 h10 h02 hlt hm2 hm1 with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨h02, le_trans h10 h02, h⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h10, le_trans h10 h02, h⟩))))
    · rcases le_total z1 z2 with h12 | h21
      · have hlt : z1 < z0 := by
          rcases lt_or_eq_of_le h10 with h | h
          · exact h
          · exfalso
            apply hne
            constructor <;> nlinarith
        rcases ordered_cycle_bad_forward hz1 h12 h20 hlt hm0 hm1 with h | h
        · exact Or.inl ⟨h10, h20, h⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h10, h12, h⟩))))
      · have hlt : z2 < z0 := by
          rcases lt_or_eq_of_le h20 with h | h
          · exact h
          · exfalso
            apply hne
            constructor <;> nlinarith
        rcases ordered_cycle_bad_backward hz2 h21 h10 hlt hm0 hm2 with h | h
        · exact Or.inl ⟨h10, h20, h⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h20, h21, h⟩))))

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
  d0_pos : 0 < d0
  d1_pos : 0 < d1
  d2_pos : 0 < d2
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

theorem allZeroCurrent0_inverse
    {m0 m1 m2 : ℕ} {d0 d1 d2 x0 x1 x2 q0 q1 q2 : ℝ}
    (h0 : -q0 + q1 + m2 * q2 - d0 * x0 = 0)
    (h1 : m0 * q0 - q1 + q2 - d1 * x1 = 0)
    (h2 : q0 + m1 * q1 - q2 - d2 * x2 = 0) :
    (m0 + m1 + m2 + m0 * m1 * m2) * q0 =
      (1 - m1) * d0 * x0 + (1 + m1 * m2) * d1 * x1 +
      (1 + m2) * d2 * x2 := by
  linear_combination
    (1 - m1) * h0 + (1 + m1 * m2) * h1 + (1 + m2) * h2

theorem allZeroCurrent1_inverse
    {m0 m1 m2 : ℕ} {d0 d1 d2 x0 x1 x2 q0 q1 q2 : ℝ}
    (h0 : -q0 + q1 + m2 * q2 - d0 * x0 = 0)
    (h1 : m0 * q0 - q1 + q2 - d1 * x1 = 0)
    (h2 : q0 + m1 * q1 - q2 - d2 * x2 = 0) :
    (m0 + m1 + m2 + m0 * m1 * m2) * q1 =
      (1 + m0) * d0 * x0 + (1 - m2) * d1 * x1 +
      (1 + m0 * m2) * d2 * x2 := by
  linear_combination
    (1 + m0) * h0 + (1 - m2) * h1 + (1 + m0 * m2) * h2

theorem allZeroCurrent2_inverse
    {m0 m1 m2 : ℕ} {d0 d1 d2 x0 x1 x2 q0 q1 q2 : ℝ}
    (h0 : -q0 + q1 + m2 * q2 - d0 * x0 = 0)
    (h1 : m0 * q0 - q1 + q2 - d1 * x1 = 0)
    (h2 : q0 + m1 * q1 - q2 - d2 * x2 = 0) :
    (m0 + m1 + m2 + m0 * m1 * m2) * q2 =
      (1 + m0 * m1) * d0 * x0 + (1 + m1) * d1 * x1 +
      (1 - m0) * d2 * x2 := by
  linear_combination
    (1 + m0 * m1) * h0 + (1 + m1) * h1 + (1 - m0) * h2

theorem ratio_le_cross_nonneg
    {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (h : a / b ≤ c / d) : 0 ≤ c * b - d * a := by
  have := (div_le_div_iff₀ hb hd).mp h
  nlinarith

theorem ratio_eq_of_cross_eq
    {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (h : c * b - d * a = 0) : a / b = c / d := by
  apply (div_eq_div_iff (ne_of_gt hb) (ne_of_gt hd)).2
  nlinarith

theorem positive_weighted_cross
    {Delta A B d e c u v : ℝ}
    (hDelta : 0 < Delta) (hA : 0 < A) (hB : 0 < B)
    (hd : 0 < d) (he : 0 < e) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hne : u ≠ 0 ∨ v ≠ 0)
    (hcross : Delta * c = A * d * u + B * e * v) : 0 < c := by
  rcases hne with hne | hne
  · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hne)
    nlinarith [mul_pos (mul_pos hA hd) hu', mul_nonneg (mul_nonneg (le_of_lt hB) (le_of_lt he)) hv]
  · have hv' : 0 < v := lt_of_le_of_ne hv (Ne.symm hne)
    nlinarith [mul_nonneg (mul_nonneg (le_of_lt hA) (le_of_lt hd)) hu, mul_pos (mul_pos hB he) hv']

theorem negative_weighted_cross
    {Delta A B d e c u v : ℝ}
    (hDelta : 0 < Delta) (hA : 0 < A) (hB : 0 < B)
    (hd : 0 < d) (he : 0 < e) (hu : u ≤ 0) (hv : v ≤ 0)
    (hne : u ≠ 0 ∨ v ≠ 0)
    (hcross : Delta * c = A * d * u + B * e * v) : c < 0 := by
  rcases hne with hne | hne
  · have hu' : u < 0 := lt_of_le_of_ne hu hne
    nlinarith [mul_neg_of_pos_of_neg (mul_pos hA hd) hu',
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (le_of_lt hB) (le_of_lt he)) hv]
  · have hv' : v < 0 := lt_of_le_of_ne hv hne
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (le_of_lt hA) (le_of_lt hd)) hu,
      mul_neg_of_pos_of_neg (mul_pos hB he) hv']

theorem eq_mul_of_div_eq {a b z : ℝ} (hb : 0 < b) (h : a / b = z) : a = z * b := by
  field_simp [ne_of_gt hb] at h
  nlinarith

theorem positive_scale_fork_forces_one
    {z y0 y1 y2 : ℝ} {m : ℕ}
    (hz : 0 < z) (hy0 : 0 < y0) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hm : 0 < m)
    (h : y0 * (z * y1) ^ m * (z * y2) -
      (z * y0) * y1 ^ m * y2 = 0) : z = 1 := by
  have hfactor : (y0 * y1 ^ m * y2 * z) * (z ^ m - 1) = 0 := by
    rw [mul_pow] at h
    linear_combination h
  have hcoef : y0 * y1 ^ m * y2 * z ≠ 0 := by positivity
  have hzpow : z ^ m = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hcoef)
  exact (pow_eq_one_iff_of_nonneg (le_of_lt hz) (Nat.ne_of_gt hm)).1 hzpow

theorem ratio_product_lt_raw
    {a b c d e f : ℝ} {m : ℕ}
    (hb : 0 < b) (hd : 0 < d) (hf : 0 < f)
    (h : (a / b) ^ m * (c / d) < e / f) :
    f * a ^ m * c < e * b ^ m * d := by
  rw [div_pow] at h
  field_simp [ne_of_gt hb, ne_of_gt hd, ne_of_gt hf] at h
  nlinarith

theorem ratio_product_gt_raw
    {a b c d e f : ℝ} {m : ℕ}
    (hb : 0 < b) (hd : 0 < d) (hf : 0 < f)
    (h : e / f < (a / b) ^ m * (c / d)) :
    e * b ^ m * d < f * a ^ m * c := by
  rw [div_pow] at h
  field_simp [ne_of_gt hb, ne_of_gt hd, ne_of_gt hf] at h
  nlinarith

theorem fork_cross_eq
    {plus minus xj xn xp yj yn yp qx qy : ℝ} {m : ℕ}
    (hqx : qx = plus * xj - minus * xn ^ m * xp)
    (hqy : qy = plus * yj - minus * yn ^ m * yp) :
    xj * qy - yj * qx = minus * (yj * xn ^ m * xp - xj * yn ^ m * yp) := by
  rw [hqx, hqy]
  ring

/-- The three-species quotient obtained when all three weak-index gaps vanish
is unistationary for arbitrary positive integer fork multiplicities. -/
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
    have cn : x.x0 * y.x1 - y.x0 * x.x1 ≠ 0 ∨
        x.x0 * y.x2 - y.x0 * x.x2 ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hzne
      exact ⟨(ratio_eq_of_cross_eq hy1 hy0 hc.1).symm,
        (ratio_eq_of_cross_eq hy1 hy0 hc.1).trans
          (ratio_eq_of_cross_eq hy2 hy0 hc.2).symm⟩
    have cp := positive_weighted_cross hDelta (by positivity) (by positivity)
      p.d1_pos p.d2_pos c1 c2 cn cross0
    have raw := ratio_product_lt_raw hy1 hy2 hy0 h.2.2
    have k := fork_cross_eq (qx := qx0) (qy := qy0)
      (by rfl) (by rfl)
    have ck : x.x0 * qy0 - y.x0 * qx0 < 0 := k.trans_lt
      (mul_neg_of_pos_of_neg p.minus0_pos (sub_neg.mpr raw))
    exact (not_lt_of_ge (le_of_lt cp)) ck
  · have c1 := ratio_le_cross_nonneg hy0 hy1 h.1
    have c2 := ratio_le_cross_nonneg hy2 hy1 h.2.1
    have cn : x.x1 * y.x0 - y.x1 * x.x0 ≠ 0 ∨
        x.x1 * y.x2 - y.x1 * x.x2 ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hzne
      exact ⟨ratio_eq_of_cross_eq hy0 hy1 hc.1,
        (ratio_eq_of_cross_eq hy2 hy1 hc.2).symm⟩
    have cp := positive_weighted_cross hDelta (by positivity) (by positivity)
      p.d0_pos p.d2_pos c1 c2 cn cross1
    have raw := ratio_product_lt_raw hy2 hy0 hy1 h.2.2
    have k := fork_cross_eq (qx := qx1) (qy := qy1)
      (by rfl) (by rfl)
    have ck : x.x1 * qy1 - y.x1 * qx1 < 0 := k.trans_lt
      (mul_neg_of_pos_of_neg p.minus1_pos (sub_neg.mpr raw))
    exact (not_lt_of_ge (le_of_lt cp)) ck
  · have c1 := ratio_le_cross_nonneg hy0 hy2 h.1
    have c2 := ratio_le_cross_nonneg hy1 hy2 h.2.1
    have cn : x.x2 * y.x0 - y.x2 * x.x0 ≠ 0 ∨
        x.x2 * y.x1 - y.x2 * x.x1 ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hzne
      exact ⟨(ratio_eq_of_cross_eq hy0 hy2 hc.1).trans
          (ratio_eq_of_cross_eq hy1 hy2 hc.2).symm,
        (ratio_eq_of_cross_eq hy1 hy2 hc.2)⟩
    have cp := positive_weighted_cross hDelta (by positivity) (by positivity)
      p.d0_pos p.d1_pos c1 c2 cn cross2
    have raw := ratio_product_lt_raw hy0 hy1 hy2 h.2.2
    have k := fork_cross_eq (qx := qx2) (qy := qy2)
      (by rfl) (by rfl)
    have ck : x.x2 * qy2 - y.x2 * qx2 < 0 := k.trans_lt
      (mul_neg_of_pos_of_neg p.minus2_pos (sub_neg.mpr raw))
    exact (not_lt_of_ge (le_of_lt cp)) ck
  · have c1 : x.x0 * y.x1 - y.x0 * x.x1 ≤ 0 := by
      have hc := ratio_le_cross_nonneg hy0 hy1 h.1
      linarith only [hc]
    have c2 : x.x0 * y.x2 - y.x0 * x.x2 ≤ 0 := by
      have hc := ratio_le_cross_nonneg hy0 hy2 h.2.1
      linarith only [hc]
    have cn : x.x0 * y.x1 - y.x0 * x.x1 ≠ 0 ∨
        x.x0 * y.x2 - y.x0 * x.x2 ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hzne
      exact ⟨(ratio_eq_of_cross_eq hy1 hy0 hc.1).symm,
        (ratio_eq_of_cross_eq hy1 hy0 hc.1).trans
          (ratio_eq_of_cross_eq hy2 hy0 hc.2).symm⟩
    have cp := negative_weighted_cross hDelta (by positivity) (by positivity)
      p.d1_pos p.d2_pos c1 c2 cn cross0
    have raw := ratio_product_gt_raw hy1 hy2 hy0 h.2.2
    have k := fork_cross_eq (qx := qx0) (qy := qy0)
      (by rfl) (by rfl)
    have ck : 0 < x.x0 * qy0 - y.x0 * qx0 := k.symm ▸
      mul_pos p.minus0_pos (sub_pos.mpr raw)
    exact (not_lt_of_ge (le_of_lt ck)) cp
  · have c1 : x.x1 * y.x0 - y.x1 * x.x0 ≤ 0 := by
      have hc := ratio_le_cross_nonneg hy1 hy0 h.1
      linarith only [hc]
    have c2 : x.x1 * y.x2 - y.x1 * x.x2 ≤ 0 := by
      have hc := ratio_le_cross_nonneg hy1 hy2 h.2.1
      linarith only [hc]
    have cn : x.x1 * y.x0 - y.x1 * x.x0 ≠ 0 ∨
        x.x1 * y.x2 - y.x1 * x.x2 ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hzne
      exact ⟨ratio_eq_of_cross_eq hy0 hy1 hc.1,
        (ratio_eq_of_cross_eq hy2 hy1 hc.2).symm⟩
    have cp := negative_weighted_cross hDelta (by positivity) (by positivity)
      p.d0_pos p.d2_pos c1 c2 cn cross1
    have raw := ratio_product_gt_raw hy2 hy0 hy1 h.2.2
    have k := fork_cross_eq (qx := qx1) (qy := qy1)
      (by rfl) (by rfl)
    have ck : 0 < x.x1 * qy1 - y.x1 * qx1 := k.symm ▸
      mul_pos p.minus1_pos (sub_pos.mpr raw)
    exact (not_lt_of_ge (le_of_lt ck)) cp
  · have c1 : x.x2 * y.x0 - y.x2 * x.x0 ≤ 0 := by
      have hc := ratio_le_cross_nonneg hy2 hy0 h.1
      linarith only [hc]
    have c2 : x.x2 * y.x1 - y.x2 * x.x1 ≤ 0 := by
      have hc := ratio_le_cross_nonneg hy2 hy1 h.2.1
      linarith only [hc]
    have cn : x.x2 * y.x0 - y.x2 * x.x0 ≠ 0 ∨
        x.x2 * y.x1 - y.x2 * x.x1 ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hzne
      exact ⟨(ratio_eq_of_cross_eq hy0 hy2 hc.1).trans
          (ratio_eq_of_cross_eq hy1 hy2 hc.2).symm,
        ratio_eq_of_cross_eq hy1 hy2 hc.2⟩
    have cp := negative_weighted_cross hDelta (by positivity) (by positivity)
      p.d0_pos p.d1_pos c1 c2 cn cross2
    have raw := ratio_product_gt_raw hy0 hy1 hy2 h.2.2
    have k := fork_cross_eq (qx := qx2) (qy := qy2)
      (by rfl) (by rfl)
    have ck : 0 < x.x2 * qy2 - y.x2 * qx2 := k.symm ▸
      mul_pos p.minus2_pos (sub_pos.mpr raw)
    exact (not_lt_of_ge (le_of_lt ck)) cp

end TypeII3

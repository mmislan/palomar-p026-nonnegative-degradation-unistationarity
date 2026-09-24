import Mathlib

namespace MixedDegradation.TypeV

def RowDefect (b c d h k r s t : ℝ) : ℝ :=
  b * (s * t - r) + c * (s - r) + d * (t - r) +
    h * r * (t - 1) + k * r * (s - 1)

theorem rowDefect_pos {b c d h k r s t : ℝ}
    (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hr : 0 < r) (hrs : r ≤ s) (hrt : r ≤ t)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hp : r < s * t) :
    0 < RowDefect b c d h k r s t := by
  have h0 := mul_pos hb (sub_pos.mpr hp)
  have h1 := mul_nonneg hc (sub_nonneg.mpr hrs)
  have h2 := mul_nonneg hd (sub_nonneg.mpr hrt)
  have h3 := mul_nonneg (mul_nonneg hh hr.le) (sub_nonneg.mpr ht)
  have h4 := mul_nonneg (mul_nonneg hk hr.le) (sub_nonneg.mpr hs)
  unfold RowDefect
  linarith only [h0, h1, h2, h3, h4]

theorem rowDefect_neg {b c d h k r s t : ℝ}
    (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hr : 0 < r) (hsr : s ≤ r) (htr : t ≤ r)
    (hs : s ≤ 1) (ht : t ≤ 1) (hp : s * t < r) :
    RowDefect b c d h k r s t < 0 := by
  have h0 := mul_neg_of_pos_of_neg hb (sub_neg.mpr hp)
  have h1 := mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr hsr)
  have h2 := mul_nonpos_of_nonneg_of_nonpos hd (sub_nonpos.mpr htr)
  have h3 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hh hr.le) (sub_nonpos.mpr ht)
  have h4 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hk hr.le) (sub_nonpos.mpr hs)
  unfold RowDefect
  linarith only [h0, h1, h2, h3, h4]

theorem ordered_ratio_side {lo mid hi : ℝ}
    (hlo : 0 < lo) (hlm : lo ≤ mid) (hmh : mid ≤ hi)
    (hne : ¬ (lo = 1 ∧ mid = 1 ∧ hi = 1)) :
    (mid ≤ 1 ∧ lo * mid < hi) ∨ (1 ≤ mid ∧ lo < mid * hi) := by
  by_cases hm : mid ≤ 1
  · left
    refine ⟨hm, ?_⟩
    have hp : lo * mid ≤ lo := by nlinarith
    by_contra h
    have heq : lo = hi := by linarith
    have hm1 : mid = 1 := by nlinarith
    apply hne
    exact ⟨by linarith, hm1, by linarith⟩
  · right
    have hm1 : 1 ≤ mid := (lt_of_not_ge hm).le
    refine ⟨hm1, ?_⟩
    have hhi : 0 < hi := hlo.trans_le (hlm.trans hmh)
    have hp : hi ≤ mid * hi := by nlinarith
    by_contra h
    have heq : lo = hi := by linarith
    have hmEq : mid = 1 := by nlinarith
    apply hne
    exact ⟨by linarith, hmEq, by linarith⟩

def SideExtremum (r0 r1 r2 : ℝ) : Prop :=
  (r1 ≤ r0 ∧ r2 ≤ r0 ∧ r1 ≤ 1 ∧ r2 ≤ 1 ∧ r1*r2 < r0) ∨
  (r2 ≤ r1 ∧ r0 ≤ r1 ∧ r2 ≤ 1 ∧ r0 ≤ 1 ∧ r2*r0 < r1) ∨
  (r0 ≤ r2 ∧ r1 ≤ r2 ∧ r0 ≤ 1 ∧ r1 ≤ 1 ∧ r0*r1 < r2) ∨
  (r0 ≤ r1 ∧ r0 ≤ r2 ∧ 1 ≤ r1 ∧ 1 ≤ r2 ∧ r0 < r1*r2) ∨
  (r1 ≤ r2 ∧ r1 ≤ r0 ∧ 1 ≤ r2 ∧ 1 ≤ r0 ∧ r1 < r2*r0) ∨
  (r2 ≤ r0 ∧ r2 ≤ r1 ∧ 1 ≤ r0 ∧ 1 ≤ r1 ∧ r2 < r0*r1)

theorem side_extremum {r0 r1 r2 : ℝ}
    (h0 : 0 < r0) (h1 : 0 < r1) (h2 : 0 < r2)
    (hne : ¬ (r0 = 1 ∧ r1 = 1 ∧ r2 = 1)) : SideExtremum r0 r1 r2 := by
  unfold SideExtremum
  rcases le_total r0 r1 with h01 | h10
  · rcases le_total r1 r2 with h12 | h21
    · have h02 := h01.trans h12
      rcases ordered_ratio_side h0 h01 h12 hne with ⟨hm,hp⟩ | ⟨hm,hp⟩
      · exact Or.inr (Or.inr (Or.inl ⟨h02,h12,h01.trans hm,hm,hp⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h01,h02,hm,hm.trans h12,hp⟩)))
    · rcases le_total r0 r2 with h02 | h20
      · have hn : ¬ (r0=1 ∧ r2=1 ∧ r1=1) := by tauto
        rcases ordered_ratio_side h0 h02 h21 hn with ⟨hm,hp⟩ | ⟨hm,hp⟩
        · exact Or.inr (Or.inl ⟨h21,h01,hm,h02.trans hm,by simpa [mul_comm] using hp⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨h01,h02,hm.trans h21,hm,by simpa [mul_comm] using hp⟩)))
      · have hn : ¬ (r2=1 ∧ r0=1 ∧ r1=1) := by tauto
        rcases ordered_ratio_side h2 h20 h01 hn with ⟨hm,hp⟩ | ⟨hm,hp⟩
        · exact Or.inr (Or.inl ⟨h21,h01,h20.trans hm,hm,hp⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨h20,h21,hm,hm.trans h01,hp⟩))))
  · rcases le_total r0 r2 with h02 | h20
    · have h12 := h10.trans h02
      have hn : ¬ (r1=1 ∧ r0=1 ∧ r2=1) := by tauto
      rcases ordered_ratio_side h1 h10 h02 hn with ⟨hm,hp⟩ | ⟨hm,hp⟩
      · exact Or.inr (Or.inr (Or.inl ⟨h02,h12,hm,h10.trans hm,by simpa [mul_comm] using hp⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨h12,h10,hm.trans h02,hm,by simpa [mul_comm] using hp⟩))))
    · rcases le_total r1 r2 with h12 | h21
      · have hn : ¬ (r1=1 ∧ r2=1 ∧ r0=1) := by tauto
        rcases ordered_ratio_side h1 h12 h20 hn with ⟨hm,hp⟩ | ⟨hm,hp⟩
        · exact Or.inl ⟨h10,h20,h12.trans hm,hm,hp⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨h12,h10,hm,hm.trans h20,hp⟩))))
      · have hn : ¬ (r2=1 ∧ r1=1 ∧ r0=1) := by tauto
        rcases ordered_ratio_side h2 h21 h10 hn with ⟨hm,hp⟩ | ⟨hm,hp⟩
        · exact Or.inl ⟨h10,h20,hm,h21.trans hm,by simpa [mul_comm] using hp⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨h20,h21,hm.trans h10,hm,by simpa [mul_comm] using hp⟩))))

structure ReducedParams where
  a : Fin 3 → ℝ
  b : Fin 3 → ℝ
  c : Fin 3 → ℝ
  d : Fin 3 → ℝ
  h : Fin 3 → ℝ
  k : Fin 3 → ℝ
  b_pos : ∀ i, 0 < b i
  c_nonneg : ∀ i, 0 ≤ c i
  d_nonneg : ∀ i, 0 ≤ d i
  h_nonneg : ∀ i, 0 ≤ h i
  k_nonneg : ∀ i, 0 ≤ k i

def ReducedStationary (p : ReducedParams) (x : Fin 3 → ℝ) : Prop :=
  ∀ i, p.a i * x i = p.b i * x (i+1) * x (i+2) +
    p.c i * x (i+1) + p.d i * x (i+2) +
    p.h i * x i * x (i+2) + p.k i * x i * x (i+1)

/-- A literal algebraic three-variable system that includes all Type V
paired-source eliminations, including zero endpoint losses and collapsed pairs. -/
theorem reduced_unistationarity (p : ReducedParams) (x y : Fin 3 → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hxs : ReducedStationary p x) (hys : ReducedStationary p y) : x = y := by
  let r : Fin 3 → ℝ := fun i => x i / y i
  have hr : ∀ i, 0 < r i := fun i => div_pos (hx i) (hy i)
  have hxry : ∀ i, x i = r i * y i := fun i =>
    (div_mul_cancel₀ (x i) (ne_of_gt (hy i))).symm
  let B := fun i => p.b i * y (i+1) * y (i+2)
  let C := fun i => p.c i * y (i+1)
  let D := fun i => p.d i * y (i+2)
  let H := fun i => p.h i * y i * y (i+2)
  let K := fun i => p.k i * y i * y (i+1)
  have hB : ∀ i, 0 < B i := fun i => mul_pos (mul_pos (p.b_pos i) (hy _)) (hy _)
  have hC : ∀ i, 0 ≤ C i := fun i => mul_nonneg (p.c_nonneg i) (hy _).le
  have hD : ∀ i, 0 ≤ D i := fun i => mul_nonneg (p.d_nonneg i) (hy _).le
  have hH : ∀ i, 0 ≤ H i := fun i => mul_nonneg (mul_nonneg (p.h_nonneg i) (hy _).le) (hy _).le
  have hK : ∀ i, 0 ≤ K i := fun i => mul_nonneg (mul_nonneg (p.k_nonneg i) (hy _).le) (hy _).le
  have hrow : ∀ i, RowDefect (B i) (C i) (D i) (H i) (K i)
      (r i) (r (i+1)) (r (i+2)) = 0 := by
    intro i
    have hxi := hxs i
    have hyi := hys i
    rw [hxry i, hxry (i+1), hxry (i+2)] at hxi
    dsimp [RowDefect, B, C, D, H, K]
    linear_combination -hxi + r i * hyi
  have hone : r 0 = 1 ∧ r 1 = 1 ∧ r 2 = 1 := by
    by_contra hne
    rcases side_extremum (hr 0) (hr 1) (hr 2) hne with
      h | h | h | h | h | h
    · have hc := rowDefect_neg (hB 0) (hC 0) (hD 0) (hH 0) (hK 0)
        (hr 0) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      have hz := hrow 0
      change RowDefect (B 0) (C 0) (D 0) (H 0) (K 0) (r 0) (r 1) (r 2) = 0 at hz
      exact (ne_of_lt hc) hz
    · have hc := rowDefect_neg (hB 1) (hC 1) (hD 1) (hH 1) (hK 1)
        (hr 1) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      have hz := hrow 1
      change RowDefect (B 1) (C 1) (D 1) (H 1) (K 1) (r 1) (r 2) (r 0) = 0 at hz
      exact (ne_of_lt hc) hz
    · have hc := rowDefect_neg (hB 2) (hC 2) (hD 2) (hH 2) (hK 2)
        (hr 2) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      have hz := hrow 2
      change RowDefect (B 2) (C 2) (D 2) (H 2) (K 2) (r 2) (r 0) (r 1) = 0 at hz
      exact (ne_of_lt hc) hz
    · have hc := rowDefect_pos (hB 0) (hC 0) (hD 0) (hH 0) (hK 0)
        (hr 0) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      have hz := hrow 0
      change RowDefect (B 0) (C 0) (D 0) (H 0) (K 0) (r 0) (r 1) (r 2) = 0 at hz
      exact (ne_of_gt hc) hz
    · have hc := rowDefect_pos (hB 1) (hC 1) (hD 1) (hH 1) (hK 1)
        (hr 1) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      have hz := hrow 1
      change RowDefect (B 1) (C 1) (D 1) (H 1) (K 1) (r 1) (r 2) (r 0) = 0 at hz
      exact (ne_of_gt hc) hz
    · have hc := rowDefect_pos (hB 2) (hC 2) (hD 2) (hH 2) (hK 2)
        (hr 2) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      have hz := hrow 2
      change RowDefect (B 2) (C 2) (D 2) (H 2) (K 2) (r 2) (r 0) (r 1) = 0 at hz
      exact (ne_of_gt hc) hz
  have hrone : ∀ i, r i = 1 := by
    intro i
    fin_cases i <;> tauto
  funext i
  rw [hxry i, hrone i, one_mul]

end MixedDegradation.TypeV

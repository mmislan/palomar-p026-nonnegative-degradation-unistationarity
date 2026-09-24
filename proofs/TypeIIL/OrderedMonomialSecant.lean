import proofs.TypeII3.Algebra.PowSecant

namespace TypeIIL

open TypeII3

/-- Product monomial for an explicitly ordered list of `(ratio, exponent)`
pairs.  The order is proof-relevant for the secant decomposition, although
the product itself is not. -/
def orderedMonomial (xs : List (ℝ × ℕ)) : ℝ :=
  (xs.map fun p => p.1 ^ p.2).prod

/-- Coordinate-ordered telescoping coefficients.  After the head factor is
expanded, every later coefficient is multiplied by the head monomial. -/
def orderedSecantCoeffs : List (ℝ × ℕ) → List ℝ
  | [] => []
  | (x, m) :: xs =>
      secantPoly x 1 m :: (orderedSecantCoeffs xs).map (x ^ m * ·)

def orderedRatioDeltas (xs : List (ℝ × ℕ)) : List ℝ :=
  xs.map fun p => p.1 - 1

def listDot (u v : List ℝ) : ℝ := (List.zipWith (· * ·) u v).sum

theorem listDot_map_mul_left (a : ℝ) (u v : List ℝ) :
    listDot (u.map (a * ·)) v = a * listDot u v := by
  induction u generalizing v with
  | nil => simp [listDot]
  | cons x u ih =>
      cases v with
      | nil => simp [listDot]
      | cons y v =>
          simp only [List.map_cons, listDot, List.zipWith_cons_cons,
            List.sum_cons]
          change a * x * y + listDot (u.map (a * ·)) v =
            a * (x * y + listDot u v)
          rw [ih v]
          ring

theorem sum_map_mul_left (a : ℝ) (u : List ℝ) :
    (u.map (a * ·)).sum = a * u.sum := by
  induction u with
  | nil => simp
  | cons x u ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem orderedSecantCoeffs_length (xs : List (ℝ × ℕ)) :
    (orderedSecantCoeffs xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons p xs ih => cases p; simp [orderedSecantCoeffs, ih]

/-- Exact coordinate-ordered monomial secant identity. -/
theorem ordered_secant_dot_ratio_deltas (xs : List (ℝ × ℕ)) :
    listDot (orderedSecantCoeffs xs) (orderedRatioDeltas xs) =
      orderedMonomial xs - 1 := by
  induction xs with
  | nil => simp [listDot, orderedSecantCoeffs, orderedRatioDeltas,
      orderedMonomial]
  | cons p xs ih =>
      rcases p with ⟨x, m⟩
      simp only [orderedSecantCoeffs, orderedRatioDeltas, orderedMonomial,
        List.map_cons, List.prod_cons, listDot, List.zipWith_cons_cons,
        List.sum_cons]
      change secantPoly x 1 m * (x - 1) +
          listDot ((orderedSecantCoeffs xs).map (x ^ m * ·))
            (orderedRatioDeltas xs) = x ^ m * orderedMonomial xs - 1
      rw [listDot_map_mul_left, ih]
      have hp := pow_sub_pow_eq_mul_secantPoly x 1 m
      simp only [one_pow] at hp
      nlinarith

/-- A positive geometric secant contains its final constant term. -/
theorem one_le_secantPoly_one {x : ℝ} (hx : 0 < x)
    {m : ℕ} (hm : 0 < m) : 1 ≤ secantPoly x 1 m := by
  induction m with
  | zero => omega
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp [secantPoly]
      · simp only [secantPoly]
        have hi := ih (Nat.pos_of_ne_zero hn)
        have hp : 0 ≤ x ^ n := le_of_lt (pow_pos hx _)
        norm_num at hi ⊢
        linarith

/-- Molecularity at least two makes the one-coordinate secant strictly
larger than one. -/
theorem one_lt_secantPoly_one {x : ℝ} (hx : 0 < x)
    {m : ℕ} (hm : 2 ≤ m) : 1 < secantPoly x 1 m := by
  cases m with
  | zero => omega
  | succ n =>
      cases n with
      | zero => omega
      | succ k =>
          rw [secantPoly]
          simp only [one_mul]
          have hp : 0 < x ^ (k + 1) := pow_pos hx _
          have ht : 1 ≤ secantPoly x 1 (k + 1) :=
            one_le_secantPoly_one hx (by omega)
          linarith

def orderedDegree (xs : List (ℝ × ℕ)) : ℕ :=
  (xs.map Prod.snd).sum

theorem orderedSecantCoeffs_sum_nonneg
    {xs : List (ℝ × ℕ)} (hpos : ∀ p ∈ xs, 0 < p.1) :
    0 ≤ (orderedSecantCoeffs xs).sum := by
  induction xs with
  | nil => simp [orderedSecantCoeffs]
  | cons p xs ih =>
      rcases p with ⟨x, m⟩
      have hx : 0 < x := hpos (x, m) (by simp)
      have htail : ∀ p ∈ xs, 0 < p.1 := by
        intro p hp
        exact hpos p (by simp [hp])
      have hi := ih htail
      have hpow : 0 ≤ x ^ m := le_of_lt (pow_pos hx _)
      have hsec : 0 ≤ secantPoly x 1 m :=
        secantPoly_nonneg hx (by norm_num) m
      simp only [orderedSecantCoeffs, List.sum_cons]
      rw [sum_map_mul_left]
      exact add_nonneg hsec (mul_nonneg hpow hi)

theorem orderedSecantCoeffs_sum_pos
    {xs : List (ℝ × ℕ)} (hpos : ∀ p ∈ xs, 0 < p.1)
    (hdegree : 0 < orderedDegree xs) :
    0 < (orderedSecantCoeffs xs).sum := by
  induction xs with
  | nil => simp [orderedDegree] at hdegree
  | cons p xs ih =>
      rcases p with ⟨x, m⟩
      change 0 < m + orderedDegree xs at hdegree
      have hx : 0 < x := hpos (x, m) (by simp)
      have htail : ∀ p ∈ xs, 0 < p.1 := by
        intro p hp
        exact hpos p (by simp [hp])
      by_cases hm : m = 0
      · subst m
        have hdTail : 0 < orderedDegree xs := by
          simpa using hdegree
        have hi := ih htail hdTail
        simpa [orderedSecantCoeffs, secantPoly, sum_map_mul_left] using hi
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hsec : 0 < secantPoly x 1 m :=
          secantPoly_pos hx (by norm_num) hmpos
        have htail0 := orderedSecantCoeffs_sum_nonneg htail
        have hpow : 0 ≤ x ^ m := le_of_lt (pow_pos hx _)
        simp only [orderedSecantCoeffs, List.sum_cons]
        rw [sum_map_mul_left]
        exact add_pos_of_pos_of_nonneg hsec (mul_nonneg hpow htail0)

/-- The ordered telescoping row has strict gain as soon as the total product
molecularity is at least two.  Unlike the logarithmic representation, this
also preserves the one-wrap sign structure seen by Schur elimination. -/
theorem one_lt_orderedSecantCoeffs_sum
    {xs : List (ℝ × ℕ)} (hpos : ∀ p ∈ xs, 0 < p.1)
    (hdegree : 2 ≤ orderedDegree xs) :
    1 < (orderedSecantCoeffs xs).sum := by
  induction xs with
  | nil => simp [orderedDegree] at hdegree
  | cons p xs ih =>
      rcases p with ⟨x, m⟩
      change 2 ≤ m + orderedDegree xs at hdegree
      have hx : 0 < x := hpos (x, m) (by simp)
      have htail : ∀ p ∈ xs, 0 < p.1 := by
        intro p hp
        exact hpos p (by simp [hp])
      by_cases hm0 : m = 0
      · subst m
        have hdTail : 2 ≤ orderedDegree xs := by
          simpa using hdegree
        have hi := ih htail hdTail
        simpa [orderedSecantCoeffs, secantPoly, sum_map_mul_left] using hi
      · by_cases hm1 : m = 1
        · subst m
          have hdTail : 0 < orderedDegree xs := by
            omega
          have htailPos := orderedSecantCoeffs_sum_pos htail hdTail
          have hxTail : 0 < x * (orderedSecantCoeffs xs).sum :=
            mul_pos hx htailPos
          simp only [orderedSecantCoeffs, secantPoly, pow_zero, one_mul,
            List.sum_cons]
          rw [sum_map_mul_left]
          linarith
        · have hm2 : 2 ≤ m := by omega
          have hsec := one_lt_secantPoly_one hx hm2
          have htail0 := orderedSecantCoeffs_sum_nonneg htail
          have hpow : 0 ≤ x ^ m := le_of_lt (pow_pos hx _)
          simp only [orderedSecantCoeffs, List.sum_cons]
          rw [sum_map_mul_left]
          nlinarith

end TypeIIL

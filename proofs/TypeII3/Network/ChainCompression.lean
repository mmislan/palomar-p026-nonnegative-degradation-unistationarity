import proofs.TypeII3.Network.Canonical

namespace TypeII3

/-- The boundary response of a unit-stoichiometric reversible chain.  Internal
degradation appears as nonnegative leakage at its two endpoints. -/
structure ChainSummary where
  c : ℝ
  beta : ℝ
  leakL : ℝ
  leakR : ℝ
  c_pos : 0 < c
  beta_pos : 0 < beta
  leakL_nonneg : 0 ≤ leakL
  leakR_nonneg : 0 ≤ leakR

/-- A chain is built by appending one reversible edge and turning the former
right endpoint into a positively degraded intermediate. -/
inductive UnitChain where
  | direct (c beta : ℝ) (c_pos : 0 < c) (beta_pos : 0 < beta)
  | extend (q : UnitChain) (c beta d : ℝ)
      (c_pos : 0 < c) (beta_pos : 0 < beta) (d_pos : 0 < d)

/-- Concentrations of the internal species, in the same recursive order as
`UnitChain`. -/
def UnitChain.State : UnitChain → Type
  | .direct _ _ _ _ => PUnit
  | .extend q _ _ _ _ _ _ => q.State × ℝ

noncomputable def UnitChain.summary : UnitChain → ChainSummary
  | .direct c beta hc hb =>
      { c := c, beta := beta, leakL := 0, leakR := 0,
        c_pos := hc, beta_pos := hb,
        leakL_nonneg := le_rfl, leakR_nonneg := le_rfl }
  | .extend q c beta d hc hb hd => by
      let s := q.summary
      let L := s.beta + s.leakR + c + d
      have hL : 0 < L := by
        dsimp [L]
        exact add_pos
          (add_pos (add_pos_of_pos_of_nonneg s.beta_pos s.leakR_nonneg) hc) hd
      exact
        { c := s.c * c / L
          beta := s.beta * beta / L
          leakL := s.leakL + s.c * (s.leakR + d) / L
          leakR := beta * (s.leakR + d) / L
          c_pos := div_pos (mul_pos s.c_pos hc) hL
          beta_pos := div_pos (mul_pos s.beta_pos hb) hL
          leakL_nonneg := add_nonneg s.leakL_nonneg
            (div_nonneg (mul_nonneg (le_of_lt s.c_pos)
              (add_nonneg s.leakR_nonneg (le_of_lt hd)))
              (le_of_lt hL))
          leakR_nonneg := div_nonneg
            (mul_nonneg (le_of_lt hb)
              (add_nonneg s.leakR_nonneg (le_of_lt hd)))
            (le_of_lt hL) }

/-- `ChainFlux q z X Y jL jR` says that the internal concentrations `z` are
steady, `jL` leaves the left endpoint, and `jR` enters the right endpoint. -/
def ChainFlux : (q : UnitChain) → q.State → ℝ → ℝ → ℝ → ℝ → Prop
  | .direct c beta _ _, _, X, Y, jL, jR =>
      jL = c * X - beta * Y ∧ jR = c * X - beta * Y
  | .extend q c beta d _ _ _, z, X, Y, jL, jR =>
      ∃ jMid,
        ChainFlux q z.1 X z.2 jL jMid ∧
        jMid - c * z.2 + beta * Y - d * z.2 = 0 ∧
        jR = c * z.2 - beta * Y

theorem two_link_shorting
    {cq bq lq rq c beta d X Y Z jL jMid jR : ℝ}
    (hbq : 0 < bq) (hrq : 0 ≤ rq)
    (hc : 0 < c) (hd : 0 < d)
    (hL : jL = (cq + lq) * X - bq * Z)
    (hR : jMid = cq * X - (bq + rq) * Z)
    (hZ : jMid - c * Z + beta * Y - d * Z = 0)
    (hOut : jR = c * Z - beta * Y) :
    let L := bq + rq + c + d
    jL = (cq * c / L + (lq + cq * (rq + d) / L)) * X -
        (bq * beta / L) * Y ∧
    jR = (cq * c / L) * X -
        (bq * beta / L + beta * (rq + d) / L) * Y := by
  dsimp
  have hden : bq + rq + c + d ≠ 0 := by
    positivity
  constructor
  · rw [hL]
    have hZformula : Z = (cq * X + beta * Y) / (bq + rq + c + d) := by
      apply (eq_div_iff hden).2
      rw [hR] at hZ
      linear_combination -hZ
    rw [hZformula]
    field_simp [hden]
    ring
  · rw [hOut]
    have hZformula : Z = (cq * X + beta * Y) / (bq + rq + c + d) := by
      apply (eq_div_iff hden).2
      rw [hR] at hZ
      linear_combination -hZ
    rw [hZformula]
    field_simp [hden]
    ring

/-- Exact compression of an arbitrary finite unit chain. -/
theorem chain_flux_compress
    (q : UnitChain) (z : q.State) {X Y jL jR : ℝ}
    (h : ChainFlux q z X Y jL jR) :
    jL = (q.summary.c + q.summary.leakL) * X - q.summary.beta * Y ∧
    jR = q.summary.c * X - (q.summary.beta + q.summary.leakR) * Y := by
  induction q generalizing X Y jL jR with
  | direct c beta hc hb =>
      simpa [ChainFlux, UnitChain.summary] using h
  | extend q c beta d hc hb hd ih =>
      rcases z with ⟨z, Z⟩
      change ∃ jMid,
        ChainFlux q z X Z jL jMid ∧
        jMid - c * Z + beta * Y - d * Z = 0 ∧
        jR = c * Z - beta * Y at h
      rcases h with ⟨jMid, hq, hZ, hOut⟩
      rcases ih z hq with ⟨hL, hR⟩
      simpa [UnitChain.summary] using
        (two_link_shorting q.summary.beta_pos
          q.summary.leakR_nonneg hc hd hL hR hZ hOut)

/-- Internal steady concentrations of a finite chain are determined by its two
endpoint concentrations.  The boundary fluxes need not be supplied. -/
theorem chain_state_unique
    (q : UnitChain) (z w : q.State) {X Y jLz jRz jLw jRw : ℝ}
    (hz : ChainFlux q z X Y jLz jRz)
    (hw : ChainFlux q w X Y jLw jRw) : z = w := by
  induction q generalizing X Y jLz jRz jLw jRw with
  | direct c beta hc hb =>
      cases z
      cases w
      rfl
  | extend q c beta d hc hb hd ih =>
      rcases z with ⟨z, Z⟩
      rcases w with ⟨w, W⟩
      change ∃ jMid,
        ChainFlux q z X Z jLz jMid ∧
        jMid - c * Z + beta * Y - d * Z = 0 ∧
        jRz = c * Z - beta * Y at hz
      change ∃ jMid,
        ChainFlux q w X W jLw jMid ∧
        jMid - c * W + beta * Y - d * W = 0 ∧
        jRw = c * W - beta * Y at hw
      rcases hz with ⟨jMidZ, hqz, hZ, _⟩
      rcases hw with ⟨jMidW, hqw, hW, _⟩
      have hfluxZ := (chain_flux_compress q z hqz).2
      have hfluxW := (chain_flux_compress q w hqw).2
      have hcoef : 0 < q.summary.beta + q.summary.leakR + c + d := by
        exact add_pos
          (add_pos (add_pos_of_pos_of_nonneg q.summary.beta_pos
            q.summary.leakR_nonneg) hc) hd
      have hZW : Z = W := by
        rw [hfluxZ] at hZ
        rw [hfluxW] at hW
        nlinarith
      subst W
      have hzw : z = w := ih z w hqz hqw
      subst w
      rfl

end TypeII3

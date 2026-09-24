import Mathlib

namespace TypeIIL

/-!
The positive-current gauge is generated locally by source balance.  At the
end of a sector, adding the back-target and fork balances cancels the return
edge and exposes a strictly positive incoming stem current.  Positivity then
propagates backwards through every positive weighted edge.  This is one
transport principle, independent of the number or pattern of stem edges.
-/

/-- The terminal back-target balance and the next-fork balance cancel the
return-edge current and force the current arriving from the stem to be
positive. -/
theorem paper_terminal_pair_incoming_current_pos
    {s jIn jTail jFork eBack eFork : ℝ}
    (hs : 0 < s) (heBack : 0 < eBack) (heFork : 0 < eFork)
    (hback : s * jIn - jTail + jFork = eBack)
    (hfork : jTail - jFork = eFork) :
    0 < jIn := by
  have hprod : 0 < s * jIn := by linarith
  exact pos_of_mul_pos_right hprod (le_of_lt hs)

/-- Positive current propagates backwards through an arbitrary weighted
stem.  `J k` is the current of edge `k`; the balance at the next species is
`s k * J k = J (k+1) + d (k+1)`. -/
theorem paper_weighted_stem_current_pos
    (m : ℕ) (s J d : ℕ → ℝ)
    (hs : ∀ k, 0 < s k) (hd : ∀ k, 0 < d k)
    (hstep : ∀ k, k < m → s k * J k = J (k + 1) + d (k + 1))
    (hterminal : 0 < J m) :
    0 < J 0 := by
  induction m generalizing s J d with
  | zero => simpa using hterminal
  | succ m ih =>
      have htail : 0 < J 1 := by
        apply ih (fun k => s (k + 1)) (fun k => J (k + 1))
          (fun k => d (k + 1))
        · intro k
          exact hs (k + 1)
        · intro k
          exact hd (k + 1)
        · intro k hk
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hstep (k + 1) (by omega)
        · simpa [Nat.add_assoc] using hterminal
      have hzero := hstep 0 (by omega)
      have hprod : 0 < s 0 * J 0 := by
        rw [hzero]
        exact add_pos htail (hd 1)
      exact pos_of_mul_pos_right hprod (le_of_lt (hs 0))

/-- Finite-index form of the same backward transport principle.  It is the
natural interface for an embedded source gap: `J i` is the current entering
coordinate `i`, and each nonterminal balance transports positivity one step
to the left. -/
theorem paper_fin_weighted_stem_current_pos
    (m : ℕ) (s J d : Fin (m + 1) → ℝ)
    (hs : ∀ i, 0 < s i) (hd : ∀ i, 0 < d i)
    (hstep : ∀ i : Fin m,
      s i.castSucc * J i.castSucc = J i.succ + d i.castSucc)
    (hterminal : 0 < J (Fin.last m)) :
    0 < J 0 := by
  induction m with
  | zero => simpa using hterminal
  | succ m ih =>
      let sTail : Fin (m + 1) → ℝ := fun i => s i.succ
      let JTail : Fin (m + 1) → ℝ := fun i => J i.succ
      let dTail : Fin (m + 1) → ℝ := fun i => d i.succ
      have hTail : 0 < JTail 0 := by
        apply ih sTail JTail dTail
        · intro i
          exact hs i.succ
        · intro i
          exact hd i.succ
        · intro i
          have h := hstep i.succ
          change s i.succ.castSucc * J i.succ.castSucc =
            J i.succ.succ + d i.succ.castSucc at h
          simpa [sTail, JTail, dTail] using h
        · simpa [JTail] using hterminal
      have hzero := hstep (0 : Fin (m + 1))
      have hzero' : s 0 * J 0 = J (Fin.succ 0) + d 0 := by
        simpa using hzero
      have hprod : 0 < s 0 * J 0 := by
        rw [hzero']
        exact add_pos (by simpa [JTail] using hTail) (hd 0)
      exact pos_of_mul_pos_right hprod (le_of_lt (hs 0))

/-- The source-level fork current is positive once the terminal balance pair
supplies positivity at the far end of its stem. -/
theorem paper_fork_current_pos_of_terminal_pair
    (m : ℕ) (s J d : ℕ → ℝ)
    {sLast jTail jNextFork eBack eNextFork : ℝ}
    (hs : ∀ k, 0 < s k) (hd : ∀ k, 0 < d k)
    (hstep : ∀ k, k < m → s k * J k = J (k + 1) + d (k + 1))
    (hsLast : 0 < sLast) (heBack : 0 < eBack)
    (heNextFork : 0 < eNextFork)
    (hback : sLast * J m - jTail + jNextFork = eBack)
    (hfork : jTail - jNextFork = eNextFork) :
    0 < J 0 := by
  apply paper_weighted_stem_current_pos m s J d hs hd hstep
  exact paper_terminal_pair_incoming_current_pos hsLast heBack heNextFork
    hback hfork

end TypeIIL

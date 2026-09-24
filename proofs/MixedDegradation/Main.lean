import proofs.MixedDegradation.TypeIISource
import proofs.MixedDegradation.TypeVSource

namespace MixedDegradation

/-- Joint source-facing resolution. Both constituent models permit literal
zero degradation constants; all reversible rate constants remain positive.
The two universal statements are independent, so neither family requires
an auxiliary witness from the other family. -/
theorem paper_mixed_degradation_unistationarity :
    (∀ (l : ℕ) (Q : TypeII.PaperRaw.OpenNetwork l),
      TypeII.PaperRaw.IsPaperTypeIILCore Q → 3 ≤ l →
      ∀ x y : Q.State, Q.PositiveState x → Q.PositiveState y →
        Q.Stationary x → Q.Stationary y → x=y) ∧
    (∀ (N : TypeV.Network) (x y : TypeV.State N),
      TypeV.PositiveState N x → TypeV.PositiveState N y →
        TypeV.Stationary N x → TypeV.Stationary N y → x=y) := by
  constructor
  · intro l Q hcore hl x y hx hy hxs hys
    exact TypeII.PaperRaw.paper_typeII_l_unistationarity Q hcore hl x y hx hy hxs hys
  · intro N x y hx hy hxs hys
    exact TypeV.paper_type_v_unistationarity N x y hx hy hxs hys

end MixedDegradation

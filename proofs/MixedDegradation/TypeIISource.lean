import proofs.TypeIIL.PaperSourceExhaustion
import proofs.MixedDegradation.TypeIILift
import proofs.MixedDegradation.Coincident

namespace MixedDegradation.TypeII

open TypeIIL TypeII3

namespace PaperRaw

open SourceCyclicNonemptyGapSystem
open PaperWeakStemSpecies

noncomputable section

/-- Literal kinetic normal data for the separated branch of the paper's
weakly ordered Type `II_l` grammar.  Main-cycle multiplicities are arbitrary
positive integers.  The optional `back` product in `source` has coefficient
one by the definition of `sourceStoich`; return reactions are the literal
unit chains carried by `rates`. -/
structure SeparatedRealization (l : ℕ) where
  n : ℕ
  next : Fin n ≃ Fin n
  back : Fin n → Option (Fin n)
  source : SourceCyclicNonemptyGapSystem (l := l) next back
  weight : Fin n → ℕ
  weight_pos : ∀ i, 0 < weight i
  rates : MixedDegradation.TypeII.Rates source weight

namespace SeparatedRealization

def State (D : SeparatedRealization l) :=
  MixedDegradation.TypeII.State D.source D.weight D.rates

def Positive (D : SeparatedRealization l) (x : D.State) : Prop :=
  MixedDegradation.TypeII.Positive x

def Stationary (D : SeparatedRealization l) (x : D.State) : Prop :=
  MixedDegradation.TypeII.Stationary D.rates x

end SeparatedRealization

/-- A source `(Top)` witness on the literal weak-stem skeleton.  This is the
paper condition before minimality: the full restricted graph is strongly
connected and contains a fork whose two products remain internal. -/
structure SourceTop {l : ℕ} (gap : Fin l → Bool) : Prop where
  stronglyConnected : ∀ a b : PaperWeakStemSpecies gap,
    Relation.ReflTransGen
      (PaperWeakStemSpecies.RestrictedEdge gap Finset.univ) a b
  internalFork : ∃ j,
    PaperWeakStemSpecies.fork gap j ∈ (Finset.univ :
      Finset (PaperWeakStemSpecies gap)) ∧
    PaperWeakStemSpecies.mainNext gap (PaperWeakStemSpecies.fork gap j) ∈
      (Finset.univ : Finset (PaperWeakStemSpecies gap)) ∧
    PaperWeakStemSpecies.backTarget gap j ∈
      (Finset.univ : Finset (PaperWeakStemSpecies gap))

/-- A total literal presentation of the paper's weak Type `II_l` source
class.  `weakGap j = false` is the weak-order coincidence
`i_j = sigma_(j+1)`.  The two kinetic records totalize the two possible
minimal normal forms; `weakGap` selects the active record, and the other is
semantically inert.  This keeps the public state type literal while allowing
nonminimal mixed weak words to be represented before source exhaustion. -/
structure OpenNetwork (l : ℕ) where
  weakGap : Fin l → Bool
  separated : SeparatedRealization l
  coincident : MixedDegradation.Coincident.AllZeroParams

/-- The generating proper source restrictions for the paper grammar.
`stem` is a chemostatted weak-stem `(Top)` core.  `tail` is a rotated proper
return subcycle with a strictly positive production flux. -/
inductive ProperSourceRestriction {l : ℕ} (Q : OpenNetwork l) : Type
  | stem (R : PaperWeakStemSpecies.ProperTopRestriction Q.weakGap)
  | tail (hsep : PaperWeakStemSpecies.AllSeparated Q.weakGap)
      (j : Fin l) (start : Fin (Q.separated.rates.tailDepth j + 1))
      (hauto : StoichiometricallyAutocatalytic
        (paperTailCycleRestriction
          (paperTailRotatedWeight
            (Q.separated.rates.tailCycleWeight j) start)))

/-- Literal source minimality under the two chemostatted restriction
generators forced by the Type `II_l` grammar. -/
def SourceMinimal {l : ℕ} (Q : OpenNetwork l) : Prop :=
  ¬ Nonempty (ProperSourceRestriction Q)

/-- Raw source predicate for a paper Type `II_l` core.  The cyclic grammar,
weak order, positive integer main weights, coefficient-one back branches,
and literal mass-action rates are data of `Q`; the two propositions here are
exactly `(Top)` and source minimality. -/
structure IsPaperTypeIILCore {l : ℕ} (Q : OpenNetwork l) : Prop where
  top : SourceTop Q.weakGap
  minimal : SourceMinimal Q

theorem stem_minimal_of_core {l : ℕ} {Q : OpenNetwork l}
    (hcore : IsPaperTypeIILCore Q) :
    PaperWeakStemSpecies.SourceMinimal Q.weakGap := by
  intro hR
  exact hcore.minimal ⟨ProperSourceRestriction.stem hR.some⟩

theorem return_minimal_of_core {l : ℕ} {Q : OpenNetwork l}
    (hcore : IsPaperTypeIILCore Q)
    (hsep : PaperWeakStemSpecies.AllSeparated Q.weakGap) :
    MixedDegradation.TypeII.ReturnMinimal Q.separated.rates := by
  intro j start hauto
  exact hcore.minimal
    ⟨ProperSourceRestriction.tail hsep j start hauto⟩

namespace OpenNetwork

/-- The literal concentration type selected by the raw weak source word.
For a source-minimal core, source exhaustion proves that the second branch
is exactly the fully coincident three-species quotient. -/
def State {l : ℕ} (Q : OpenNetwork l) : Type :=
  @ite Type (PaperWeakStemSpecies.AllSeparated Q.weakGap)
    (Classical.propDecidable _) Q.separated.State MixedDegradation.Coincident.AllZeroState

def separatedStateEquiv {l : ℕ} (Q : OpenNetwork l)
    (hsep : PaperWeakStemSpecies.AllSeparated Q.weakGap) :
    Q.State ≃ Q.separated.State :=
  Equiv.cast (by simp [State, hsep])

def coincidentStateEquiv {l : ℕ} (Q : OpenNetwork l)
    (hsep : ¬ PaperWeakStemSpecies.AllSeparated Q.weakGap) :
    Q.State ≃ MixedDegradation.Coincident.AllZeroState :=
  Equiv.cast (by simp [State, hsep])

def ExceptionalBranch {l : ℕ} (Q : OpenNetwork l) : Prop :=
  l = 3 ∧ PaperWeakStemSpecies.AllCoincident Q.weakGap

def PositiveState {l : ℕ} (Q : OpenNetwork l) (x : Q.State) : Prop :=
  @dite Prop (PaperWeakStemSpecies.AllSeparated Q.weakGap)
    (Classical.propDecidable _)
    (fun hsep => Q.separated.Positive (Q.separatedStateEquiv hsep x))
    (fun hsep => Q.ExceptionalBranch ∧
      MixedDegradation.Coincident.PositiveAllZeroState (Q.coincidentStateEquiv hsep x))

def Stationary {l : ℕ} (Q : OpenNetwork l) (x : Q.State) : Prop :=
  @dite Prop (PaperWeakStemSpecies.AllSeparated Q.weakGap)
    (Classical.propDecidable _)
    (fun hsep => Q.separated.Stationary (Q.separatedStateEquiv hsep x))
    (fun hsep => Q.ExceptionalBranch ∧
      MixedDegradation.Coincident.IsAllZeroStationary Q.coincident (Q.coincidentStateEquiv hsep x))

end OpenNetwork

/-- Source exhaustion for the literal raw paper predicate. -/
theorem core_exhaustion {l : ℕ} (Q : OpenNetwork l)
    (hcore : IsPaperTypeIILCore Q) (hl : 3 ≤ l) :
    PaperWeakStemSpecies.AllSeparated Q.weakGap ∨
      (l = 3 ∧ PaperWeakStemSpecies.AllCoincident Q.weakGap) :=
  PaperWeakStemSpecies.source_exhaustion_of_minimal Q.weakGap hl
    (stem_minimal_of_core hcore)

/-- Nonnegative-loss terminal source theorem.  Its public boundary contains the raw
paper core, positivity, and literal stationary equations only. Tail
minimality and cyclic predecessor separation are derived internally; the
boundary argument and chain reconstruction are supplied by the family proof. -/
theorem paper_typeII_l_unistationarity
    {l : ℕ} (Q : OpenNetwork l) (hcore : IsPaperTypeIILCore Q)
    (hl : 3 ≤ l) (x y : Q.State)
    (hx : Q.PositiveState x) (hy : Q.PositiveState y)
    (hxs : Q.Stationary x) (hys : Q.Stationary y) : x = y := by
  have hclass := core_exhaustion Q hcore hl
  by_cases hsep : PaperWeakStemSpecies.AllSeparated Q.weakGap
  · let e := Q.separatedStateEquiv hsep
    apply e.injective
    apply MixedDegradation.TypeII.separated_unistationarity Q.separated.source
      hl Q.separated.weight Q.separated.weight_pos Q.separated.rates
      (return_minimal_of_core hcore hsep)
    · simpa [OpenNetwork.PositiveState, hsep, e] using hx
    · simpa [OpenNetwork.PositiveState, hsep, e] using hy
    · simpa [OpenNetwork.Stationary, hsep, e] using hxs
    · simpa [OpenNetwork.Stationary, hsep, e] using hys
  · have hexception :
        l = 3 ∧ PaperWeakStemSpecies.AllCoincident Q.weakGap :=
      hclass.resolve_left hsep
    let e := Q.coincidentStateEquiv hsep
    apply e.injective
    apply MixedDegradation.Coincident.all_zero_unistationarity Q.coincident
    · simpa [OpenNetwork.PositiveState, OpenNetwork.ExceptionalBranch,
        hsep, hexception, e] using hx
    · simpa [OpenNetwork.PositiveState, OpenNetwork.ExceptionalBranch,
        hsep, hexception, e] using hy
    · simpa [OpenNetwork.Stationary, OpenNetwork.ExceptionalBranch,
        hsep, hexception, e] using hxs
    · simpa [OpenNetwork.Stationary, OpenNetwork.ExceptionalBranch,
        hsep, hexception, e] using hys

end

end PaperRaw

end MixedDegradation.TypeII

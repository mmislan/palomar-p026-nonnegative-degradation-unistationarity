import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Type II_l and Type V uniqueness with nonnegative degradation

Literature problem 12. Both literal source families allow zero degradation
rates, while reversible reaction rates remain positive. Uniqueness concerns
positive stationary states and does not assume their existence. Type II_l
retains the raw source-minimality predicate; Type V retains all path species.
-/

noncomputable section
namespace TypeII3
structure ChainSummary where
  c : ℝ
  beta : ℝ
  leakL : ℝ
  leakR : ℝ
  c_pos : 0 < c
  beta_pos : 0 < beta
  leakL_nonneg : 0 ≤ leakL
  leakR_nonneg : 0 ≤ leakR

def StoichiometricallyAutocatalytic {n r : ℕ}
    (S : Fin n → Fin r → ℝ) : Prop :=
  ∃ v : Fin r → ℝ, (∀ j, 0 < v j) ∧
    ∀ i, 0 < ∑ j, S i j * v j

end TypeII3
namespace TypeIIL
open TypeII3
open scoped BigOperators

def finitePathPrev {m : ℕ} (i : Fin (m + 1)) (h : 0 < i.val) : Fin (m + 1) :=
  ⟨i.val - 1, by omega⟩

def finitePathNext {m : ℕ} (i : Fin (m + 1)) (h : i.val < m) : Fin (m + 1) :=
  ⟨i.val + 1, by omega⟩

structure SourceGapEmbedding {n : ℕ}
    (next : Fin n ≃ Fin n) (back : Fin n → Option (Fin n)) (m : ℕ) where
  idx : Fin (m + 1) ↪ Fin n
  nonfork : ∀ i, back (idx i) = none
  successor_support : ∀ i j,
    next (idx i) = idx j ↔
      ∃ h : i.val < m, j = finitePathNext i h
  predecessor_support : ∀ i j,
    next (idx j) = idx i ↔
      ∃ h : 0 < i.val, j = finitePathPrev i h
  no_two_cycle : ∀ x, x ≠ next (next x)

structure SourcePreForkGap
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (fork : Fin n) where
  terminal_next : next (G.idx (Fin.last m)) = fork
  fork_back : back fork = some (G.idx (Fin.last m))
  fork_successor_outside : ∀ i, next fork ≠ G.idx i
  fork_ne_next : fork ≠ next fork

structure SourcePostForkGap
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m) (fork z : Fin n) where
  first_eq : G.idx 0 = next fork
  fork_back : back fork = some z
  fork_outside : ∀ i, fork ≠ G.idx i
  fork_not_successor : ∀ i, fork ≠ next (G.idx i)
  back_outside : ∀ i, z ≠ G.idx i
  back_not_successor : ∀ i, z ≠ next (G.idx i)

structure SourceWrapForkGap
    {n m : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}
    (G : SourceGapEmbedding next back m)
    (left right leftBack : Fin n) where
  pre : SourcePreForkGap G right
  post : SourcePostForkGap G left leftBack
  right_successor_ne_left : next right ≠ left
  right_successor_ne_leftBack : next right ≠ leftBack
  right_ne_leftBack : right ≠ leftBack

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

def sourceProductExponent {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) : Fin n → Fin n → ℕ :=
  fun i r => (if i = next r then weight r else 0) +
    match back r with
    | none => 0
    | some z => if i = z then 1 else 0

def sourceStoich {n : ℕ}
    (next : Fin n → Fin n) (weight : Fin n → ℕ)
    (back : Fin n → Option (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => (sourceProductExponent next weight back i k : ℝ) -
    if i = k then 1 else 0

abbrev PaperSourceState (n : ℕ) := Fin n → ℝ

def paperSourceProductMonomial {n : ℕ}
    (P : Fin n → Fin n → ℕ) (r : Fin n)
    (x : PaperSourceState n) : ℝ :=
  ∏ i, x i ^ P i r

def paperTailCycleRestriction {N : ℕ} (weight : Fin N → ℕ) :
    Fin N → Fin N → ℝ :=
  fun i j =>
    (if i = j then -1 else 0) +
      (if i = finRotate N j then (weight j : ℝ) else 0)

def paperTailRotatedWeight {N : ℕ} (weight : Fin N → ℕ)
    (start : Fin N) : Fin N → ℕ :=
  fun j => weight (finCycle start j)

namespace SourceCyclicNonemptyGapSystem
variable {n l : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}

def paperTailTerminal
    (S : SourceCyclicNonemptyGapSystem (l := l) next back) (j : Fin l) :
    Fin n :=
  (S.gap (S.step.symm j)).idx
    (Fin.last (S.gapLength (S.step.symm j)))

def paperTailBoundaryContribution
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (i : Fin n) (j : Fin l) (jL jR : ℝ) : ℝ :=
  (if i = S.paperTailTerminal j then -jL else 0) +
    (if i = S.fork j then jR else 0)

end SourceCyclicNonemptyGapSystem

def PaperWeakStemSpecies {l : ℕ} (gap : Fin l → Bool) :=
  Fin l ⊕ {j : Fin l // gap j = true}

noncomputable instance paperWeakStemSubtypeFintype {l : ℕ}
    (gap : Fin l → Bool) : Fintype {j : Fin l // gap j = true} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance paperWeakStemSpeciesFintype {l : ℕ}
    (gap : Fin l → Bool) : Fintype (PaperWeakStemSpecies gap) := by
  unfold PaperWeakStemSpecies
  infer_instance

noncomputable instance paperWeakStemSpeciesDecidableEq {l : ℕ}
    (gap : Fin l → Bool) : DecidableEq (PaperWeakStemSpecies gap) :=
  Classical.decEq _

namespace PaperWeakStemSpecies

variable {l : ℕ} (gap : Fin l → Bool)

def fork (j : Fin l) : PaperWeakStemSpecies gap := Sum.inl j

/-- The back target `sigma_(j+1)` at the end of the stem leaving fork `j`.
For a coincident stem this is the fork itself. -/
noncomputable def stemEnd (j : Fin l) : PaperWeakStemSpecies gap :=
  if h : gap j = true then Sum.inr ⟨j, h⟩ else Sum.inl j

/-- Target of the main-cycle product after contracting the return path. -/
noncomputable def mainNext : PaperWeakStemSpecies gap → PaperWeakStemSpecies gap
  | Sum.inl j =>
      if gap j = true then stemEnd gap j else fork gap (finRotate l j)
  | Sum.inr j => fork gap (finRotate l j.1)

/-- Coefficient-one back product of the fork reaction at `j`. -/
noncomputable def backTarget (j : Fin l) : PaperWeakStemSpecies gap :=
  stemEnd gap ((finRotate l).symm j)

/-- Split-graph edges of the source Type `II_l` skeleton. -/
inductive SplitEdge : PaperWeakStemSpecies gap → PaperWeakStemSpecies gap → Prop
  | main (a) : SplitEdge a (mainNext gap a)
  | back (j) : SplitEdge (fork gap j) (backTarget gap j)

def RestrictedEdge (species : Finset (PaperWeakStemSpecies gap))
    (a b : PaperWeakStemSpecies gap) : Prop :=
  a ∈ species ∧ b ∈ species ∧ SplitEdge gap a b

/-- An explicit proper chemostatted restriction satisfying `(Top)`: its
retained split graph is strongly connected and one retained fork reaction
keeps both of its products.  This is exactly the source convention after
removing reactions with all reactants or all products outside. -/
structure ProperTopRestriction where
  species : Finset (PaperWeakStemSpecies gap)
  proper : species ≠ Finset.univ
  stronglyConnected : ∀ {a}, a ∈ species → ∀ {b}, b ∈ species →
    Relation.ReflTransGen (RestrictedEdge gap species) a b
  internalFork : ∃ j,
    fork gap j ∈ species ∧ mainNext gap (fork gap j) ∈ species ∧
      backTarget gap j ∈ species

/-- Source minimality on the weak-stem skeleton: no proper chemostatted
species restriction retains `(Top)`. -/
def SourceMinimal : Prop := ¬ Nonempty (ProperTopRestriction gap)

def AllSeparated : Prop := ∀ j, gap j = true

def AllCoincident : Prop := ∀ j, gap j = false

end PaperWeakStemSpecies
end TypeIIL

namespace MixedDegradation
open TypeII3
inductive UnitChain where
  | direct (c beta : ℝ) (c_pos : 0 < c) (beta_pos : 0 < beta)
  | extend (q : UnitChain) (c beta d : ℝ)
      (c_pos : 0 < c) (beta_pos : 0 < beta) (d_nonneg : 0 ≤ d)

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
        exact add_pos_of_pos_of_nonneg
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
              (add_nonneg s.leakR_nonneg hd))
              (le_of_lt hL))
          leakR_nonneg := div_nonneg
            (mul_nonneg (le_of_lt hb)
              (add_nonneg s.leakR_nonneg hd))
            (le_of_lt hL) }

def ChainFlux : (q : UnitChain) → q.State → ℝ → ℝ → ℝ → ℝ → Prop
  | .direct c beta _ _, _, X, Y, jL, jR =>
      jL = c * X - beta * Y ∧ jR = c * X - beta * Y
  | .extend q c beta d _ _ _, z, X, Y, jL, jR =>
      ∃ jMid,
        ChainFlux q z.1 X z.2 jL jMid ∧
        jMid - c * z.2 + beta * Y - d * z.2 = 0 ∧
        jR = c * z.2 - beta * Y

end MixedDegradation

namespace MixedDegradation.Coincident
open TypeII3
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

end MixedDegradation.Coincident

namespace MixedDegradation.TypeII
open TypeIIL TypeII3
open TypeIIL.SourceCyclicNonemptyGapSystem
open scoped BigOperators
variable {n l : ℕ} {next : Fin n ≃ Fin n} {back : Fin n → Option (Fin n)}

structure Rates (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) where
  tailDepth : Fin l → ℕ
  tailDepth_pos : ∀ j, 1 ≤ tailDepth j
  tailCycleWeight : ∀ j, Fin (tailDepth j+1) → ℕ
  tailCycleWeight_pos : ∀ j k, 0 < tailCycleWeight j k
  terminal_cycle_weight : ∀ j, weight (S.paperTailTerminal j) = tailCycleWeight j 0
  chain : Fin l → MixedDegradation.UnitChain
  plus : Fin n → ℝ
  minus : Fin n → ℝ
  degrade : Fin n → ℝ
  plus_pos : ∀ r, 0 < plus r
  minus_pos : ∀ r, 0 < minus r
  degrade_nonneg : ∀ i, 0 ≤ degrade i
  terminal_plus : ∀ j, plus (S.paperTailTerminal j) = (chain j).summary.c
  terminal_minus : ∀ j, minus (S.paperTailTerminal j) = (chain j).summary.beta

@[ext] structure State (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (weight : Fin n → ℕ) (rates : Rates S weight) where
  core : Fin n → ℝ
  tail : ∀ j, (rates.chain j).State

def positiveTail : (q : MixedDegradation.UnitChain) → q.State → Prop
  | .direct _ _ _ _, _ => True
  | .extend q _ _ _ _ _ _, z => positiveTail q z.1 ∧ 0 < z.2

def Positive {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} {rates : Rates S weight} (x : State S weight rates) : Prop :=
  (∀ i, 0 < x.core i) ∧ ∀ j, positiveTail (rates.chain j) (x.tail j)

def current {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : Rates S weight) (x : Fin n → ℝ) (r : Fin n) : ℝ :=
  rates.plus r*x r-rates.minus r*paperSourceProductMonomial (sourceProductExponent next weight back) r x

def Stationary {S : SourceCyclicNonemptyGapSystem (l := l) next back}
    {weight : Fin n → ℕ} (rates : Rates S weight) (x : State S weight rates) : Prop :=
  ∃ jL jR : Fin l → ℝ,
    (∀ j, MixedDegradation.ChainFlux (rates.chain j) (x.tail j)
      (x.core (S.paperTailTerminal j)) (x.core (S.fork j)) (jL j) (jR j)) ∧
    ∀ i, (∑ r, sourceStoich next weight back i r*current rates x.core r) -
      (∑ j, sourceStoich next weight back i (S.paperTailTerminal j)*current rates x.core (S.paperTailTerminal j)) +
      (∑ j, paperTailBoundaryContribution S i j (jL j) (jR j)) = rates.degrade i*x.core i

namespace PaperRaw
open SourceCyclicNonemptyGapSystem PaperWeakStemSpecies

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

end PaperRaw
end MixedDegradation.TypeII

namespace MixedDegradation.TypeV
inductive Sector where
  | collapsed
  | linked (chain : MixedDegradation.UnitChain) (loss : ℝ) (loss_nonneg : 0 ≤ loss)

def Sector.Aux : Sector → Type
  | .collapsed => PUnit
  | .linked q _ _ => ℝ × q.State

def Sector.tip : (q : Sector) → ℝ → q.Aux → ℝ
  | .collapsed, X, _ => X
  | .linked _ _ _, _, z => z.1

def Sector.current (q : Sector) (f g X P : ℝ) (z : q.Aux) : ℝ :=
  f * q.tip X z - g * P

def Sector.Steady : (q : Sector) → ℝ → ℝ → ℝ → ℝ → ℝ → q.Aux → ℝ → Prop
  | .collapsed, f, g, d, X, P, z, T =>
      T - Sector.current .collapsed f g X P z - d * X = 0
  | .linked q loss hl, f, g, d, X, P, z, T =>
      ∃ jL jR, MixedDegradation.ChainFlux q z.2 X z.1 jL jR ∧
        jR - Sector.current (.linked q loss hl) f g X P z - loss * z.1 = 0 ∧
        T - jL - d * X = 0

structure Network where
  sector : Fin 3 → Sector
  forward : Fin 3 → ℝ
  reverse : Fin 3 → ℝ
  loss : Fin 3 → ℝ
  forward_pos : ∀ i, 0 < forward i
  reverse_pos : ∀ i, 0 < reverse i
  loss_nonneg : ∀ i, 0 ≤ loss i

@[ext] structure State (N : Network) where
  base : Fin 3 → ℝ
  aux : ∀ i, (N.sector i).Aux

def current (N : Network) (x : State N) (i : Fin 3) : ℝ :=
  (N.sector i).current (N.forward i) (N.reverse i) (x.base i)
    (x.base (i+1)*x.base (i+2)) (x.aux i)

def Stationary (N : Network) (x : State N) : Prop :=
  ∀ i, (N.sector i).Steady (N.forward i) (N.reverse i) (N.loss i)
    (x.base i) (x.base (i+1)*x.base (i+2)) (x.aux i)
    (current N x (i+1)+current N x (i+2))

def chainPositive : (q : MixedDegradation.UnitChain) → q.State → Prop
  | .direct _ _ _ _, _ => True
  | .extend q _ _ _ _ _ _, z => chainPositive q z.1 ∧ 0 < z.2

def Sector.positiveAux : (q : Sector) → q.Aux → Prop
  | .collapsed, _ => True
  | .linked q _ _, z => 0 < z.1 ∧ chainPositive q z.2

def PositiveState (N : Network) (x : State N) : Prop :=
  (∀ i, 0 < x.base i) ∧ ∀ i, (N.sector i).positiveAux (x.aux i)

end MixedDegradation.TypeV

namespace MixedDegradation
theorem paper_mixed_degradation_unistationarity :
    (∀ (l : ℕ) (Q : TypeII.PaperRaw.OpenNetwork l),
      TypeII.PaperRaw.IsPaperTypeIILCore Q → 3 ≤ l →
      ∀ x y : Q.State, Q.PositiveState x → Q.PositiveState y →
        Q.Stationary x → Q.Stationary y → x=y) ∧
    (∀ (N : TypeV.Network) (x y : TypeV.State N),
      TypeV.PositiveState N x → TypeV.PositiveState N y →
        TypeV.Stationary N x → TypeV.Stationary N y → x=y) := by
  sorry

end MixedDegradation
end

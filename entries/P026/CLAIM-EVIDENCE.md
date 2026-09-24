# P026: claim-to-evidence correspondence

Source-reading review dated 2026-09-24. No Lean was executed for this review.

## Selected declaration

`MixedDegradation.paper_mixed_degradation_unistationarity` in
[`Registry/P026/Challenge.lean`](../../Registry/P026/Challenge.lean) is the
conjunction of two independent universal statements:

1. For every `l : ℕ` and every `Q : TypeII.PaperRaw.OpenNetwork l`, if
   `IsPaperTypeIILCore Q` and `3 ≤ l`, then for all `x y : Q.State`,
   `Q.PositiveState x → Q.PositiveState y → Q.Stationary x → Q.Stationary y → x = y`.
2. For every `N : TypeV.Network` and all `x y : TypeV.State N`,
   `TypeV.PositiveState N x → TypeV.PositiveState N y →
   TypeV.Stationary N x → TypeV.Stationary N y → x = y`.

Both conclusions are uniqueness (at most one) statements. Neither asserts that
a positive stationary state exists, or anything about stability.

| Claim component | Exact formal condition in the Challenge |
| --- | --- |
| Network class, Type II_l | `OpenNetwork l`: a Boolean weak-stem word `weakGap`, a separated realization (cyclic source gap system, positive integer main weights `weight`, coefficient-one back products, return chains) and a coincident three-species parameter record. |
| Source-minimal core, Type II_l | `IsPaperTypeIILCore Q` = `SourceTop Q.weakGap` (strongly connected split graph with an internal fork) and `SourceMinimal Q` (no `ProperSourceRestriction`: neither a proper weak-stem `(Top)` restriction nor, when all stems are separated, a rotated return cycle that is `StoichiometricallyAutocatalytic`). Also `3 ≤ l`. |
| Network class, Type V | `TypeV.Network`: three sectors, each `collapsed` or `linked` with an arbitrary finite `UnitChain` and a fork-source loss `loss ≥ 0`. There is no separate minimality hypothesis; the normal form itself is the class. |
| Rate constants | Strictly positive: `Rates.plus_pos`, `Rates.minus_pos`, `UnitChain` `c_pos`/`beta_pos`, `AllZeroParams.plus*_pos`/`minus*_pos`, `Network.forward_pos`/`reverse_pos`. |
| Degradation | Only nonnegative: `Rates.degrade_nonneg` (every retained species), `UnitChain.extend` `d_nonneg` (every internal chain species), `AllZeroParams.d*_nonneg`, `Network.loss_nonneg`, `Sector.linked` `loss_nonneg`. Any subset of these, including all of them, may be zero; the positive vector is also allowed. |
| Stationarity | Literal balance equations of the active branch, including every internal return-chain or path species (`ChainFlux`, `TypeII.Stationary`, `IsAllZeroStationary`, `TypeV.Stationary`). |
| Positivity | Every concentration, including internal chain species (`positiveTail`, `chainPositive`, `Sector.positiveAux`), must be strictly positive. |
| Conclusion | `x = y` on the full literal state (core plus every internal chain coordinate). |

Branch encoding (Type II_l). `Q.State`, `Q.PositiveState` and `Q.Stationary`
select the separated realization when `AllSeparated Q.weakGap`. Otherwise both
predicates require `ExceptionalBranch` (`l = 3` and all stems coincident) and use
the three-species coincident record. For a non-separated word that is not
exceptional, `PositiveState` is false, so the first conjunct holds vacuously
there. That such words are never source-minimal for `l ≥ 3` is the inherited
lemma `TypeIIL.PaperWeakStemSpecies.source_exhaustion_of_minimal`, which is in the
Solution import closure but is not part of the selected statement. The name
`AllZeroParams`/`all_zero_unistationarity` refers to the all-coincident stem
word, not to zero degradation (manuscript, Table 1 caption).

Return paths (Type II_l). Return paths are modelled kinetically as reversible
unit chains (`UnitChain`), whose stationary effect enters the core balance through
`paperTailBoundaryContribution`. The core terminal reaction's own current is
subtracted, so `terminal_plus`/`terminal_minus` only tie inert placeholders to the
chain summary. The multipliers `tailCycleWeight` enter only the minimality
predicate, through `ProperSourceRestriction.tail`. This matches manuscript
Lemma 2.2: source minimality forces unit return paths.

## Correspondence to the manuscript

The selected declaration is the formal counterpart of the companion
manuscript's Theorem 1.1 (Main theorem), restricted to the two families it
names: source-minimal Type II_l cores with l ≥ 3 and the literal Type V
normal forms (with no separate minimality hypothesis), with positive forward and reverse mass-action rates and a nonnegative
degradation vector. The manuscript's formal-verification section prints the
same statement. Supporting steps that are formal inside the Solution closure
include:

- Lemma 3.1 (passive-path reduction)
- the Type V three-ratio argument (Lemma 4.1)
- the stationary factorization and the boundary nonsingularity theorem (Theorem 6.5)
- the implicit-function uniqueness transfer (Lemma 7.1)
- the coincident branch (Proposition 7.2)
- source exhaustion (Lemma 2.1)

The interior positive-degradation criterion of the Type II_l development
(`proofs/TypeIIL`) is imported and proved in the closure. It is not assumed.

Evidence: historical receipt only. `papers/P026/claims.json` records a
Lean 4.30.0 receipt for `proofs/MixedDegradation/Main.lean`
(`migration/historical-receipts/d23fbd12c0850234df0a.json`), with axioms
`propext`, `Classical.choice`, `Quot.sound`. On the target toolchain only the
Challenge statement has been compiled
([statement check](statement-check.json)). This check does not cover the proof.
`Registry/P026/Solution.lean` is the single line `import proofs.MixedDegradation.Main`.

## Literature correspondence

Primary source: P. Nandan, P. Nghe and J. Unterberger, *Autocatalytic cores in
the diluted regime: classification and properties*, Journal of Mathematical
Biology 92 (2026), article 36, doi:10.1007/s00285-026-02357-7, arXiv:2507.15546.
The companion manuscript cites the remark after their Theorem 5.2. There the
authors raise mixed degradation, where some species are degraded and others
are not, and note that their argument does not settle it for Type V or for
Type II_l with l > 2.

The entry settles that question as posed, but only for these two families. For
the reversible mass-action extension of each such source-minimal core, positive
reversible rates and any nonnegative degradation vector give at most one
strictly positive stationary state. This is **not** an unconditional extension
of positive-degradation uniqueness:

- it requires source minimality (`IsPaperTypeIILCore`) for Type II_l and `l ≥ 3`;
- it covers only the literal source normal forms encoded in the Challenge.

The companion Type II_l paper reports that nonminimal networks can be
multistationary. The step identifying these normal forms with the prose
classification of Nandan–Nghe–Unterberger is conventional mathematics in the
manuscript, not formal. The five-family corollary (Corollary 1.2) relies on
cited published results for the other families and is not formalized.

This is an agent-assisted source reading, not an independent human review.

## Evidence boundary

- Not formalized: existence of a positive stationary state; stability; the
  quantitative determinant bound; local continuation; small-degradation
  existence and stability (Section 8); the identification of the Lean normal
  forms with the published classification; Corollary 1.2.
- Nonminimal Type II_l networks, Type II_l with `l < 3`, and cores coupled to
  other reactions are outside the statement.
- Coverage of the non-separated Type II_l case relies on the branch gating
  described above together with `source_exhaustion_of_minimal`.
- The Solution closure (90 modules including `Registry.P026.Solution`) contains
  `problem_workspaces/RAF_full_type_II_l_closure/SingletonSpliceScratch.lean`,
  imported from `proofs/TypeIIL/SourceBackFirstWeakClosure.lean`. It lives
  outside `proofs/` and must be shipped with any release candidate.
- A text grep of that closure found no `sorry`, `admit` or `axiom` tokens. This
  grep does not replace an axiom check.
- The target Solution compilation, Comparator run and independent kernel checks
  are pending. `entries/P026/readiness.json` records them as `NOT_RUN`.

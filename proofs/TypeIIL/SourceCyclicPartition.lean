import proofs.TypeIIL.SourceCyclicGapSystem

namespace TypeIIL

open scoped BigOperators

namespace SourceCyclicNonemptyGapSystem

variable {n l : ℕ} {next : Fin n ≃ Fin n}
  {back : Fin n → Option (Fin n)}

/-- The paper-shaped cyclic cover is not merely surjective: the fork vertices
and all owned gap vertices form a disjoint coordinate system for the species. -/
noncomputable def vertexEquiv
    (S : SourceCyclicNonemptyGapSystem (l := l) next back) :
    (Fin l ⊕ (Σ a : Fin l, Fin (S.gapLength a + 1))) ≃ Fin n :=
  Equiv.ofBijective
    (fun v => match v with
      | Sum.inl a => S.fork a
      | Sum.inr ai => (S.gap ai.1).idx ai.2)
    (by
      constructor
      · intro u v huv
        rcases u with a | ⟨a, i⟩ <;> rcases v with b | ⟨b, j⟩
        · exact congrArg Sum.inl (S.fork.injective huv)
        · exact False.elim (S.gap_point_ne_fork a b j huv.symm)
        · exact False.elim (S.gap_point_ne_fork b a i huv)
        · apply congrArg Sum.inr
          by_cases hab : a = b
          · subst b
            have hij : i = j := (S.gap a).idx.injective huv
            subst j
            rfl
          · exact False.elim (S.gap_point_ne_other_gap hab i j huv)
      · intro k
        rcases S.cover k with ⟨a, ha⟩ | ⟨a, i, hi⟩
        · exact ⟨Sum.inl a, ha.symm⟩
        · exact ⟨Sum.inr ⟨a, i⟩, hi.symm⟩)

/-- Any full species sum splits canonically into its fork and gap parts. -/
theorem sum_eq_fork_sum_add_gap_sum
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (f : Fin n → ℝ) :
    (∑ k, f k) =
      (∑ a, f (S.fork a)) + ∑ a, ∑ i, f ((S.gap a).idx i) := by
  classical
  rw [← (S.vertexEquiv.sum_comp f)]
  simp [vertexEquiv, Equiv.ofBijective, Fintype.sum_sigma]

end SourceCyclicNonemptyGapSystem

end TypeIIL

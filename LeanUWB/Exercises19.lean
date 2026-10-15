import LeanUWB.Exercises18


variable {I J F : Type} [Fintype I] [Fintype J] [Field F] [LinearOrder F] [IsStrictOrderedRing F]

open scoped Matrix

/-- A system of linear inequalities has a nonnegative solution if and only if
we cannot obtain a contradiction by taking a linear combination of the inequalities. -/
theorem inequalityFarkas (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → F, 0 ≤ y ∧ 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0) := by
  classical
  sorry

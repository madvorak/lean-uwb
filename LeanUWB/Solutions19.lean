import LeanUWB.Solutions18


variable {I J F : Type} [Fintype I] [Fintype J] [Field F] [LinearOrder F] [IsStrictOrderedRing F]

open scoped Matrix

/-- A system of linear inequalities has a nonnegative solution if and only if
we cannot obtain a contradiction by taking a linear combination of the inequalities. -/
theorem inequalityFarkas (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → F, 0 ≤ y ∧ 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0) := by
  classical
  let A' : Matrix I (I ⊕ J) F := Matrix.fromCols 1 A
  convert equalityFarkas A' b using 1
  · constructor
    · intro ⟨x, hx, hAxb⟩
      use Sum.elim (b - A *ᵥ x) x
      constructor
      · rw [Sum.nonneg_elim_iff]
        constructor
        · intro
          simp
          apply hAxb
        · exact hx
      · simp [A']
    · intro ⟨x, hx, hAxb⟩
      use x ∘ Sum.inr
      constructor
      · intro
        apply hx
      · intro i
        have hi := congr_fun hAxb i
        simp only [A', Matrix.fromCols_mulVec, Pi.add_apply] at hi
        have : 0 ≤ (1 *ᵥ x ∘ Sum.inl) i
        · simpa using hx (Sum.inl i)
        linarith
  · constructor
    · intro ⟨y, hy, hAy, hby⟩
      refine ⟨y, ?_, hby⟩
      intro k
      cases k with
      | inl i => exact dotProduct_nonneg_of_nonneg (Matrix.zero_le_one_elem · i) hy
      | inr j => apply hAy
    · intro ⟨y, hAy, hby⟩
      have h1Ay : 0 ≤ Matrix.fromRows (1 : Matrix I I F) Aᵀ *ᵥ y
      · simpa [A', Matrix.transpose_fromCols, Matrix.transpose_one] using hAy
      refine ⟨y, fun i : I => ?_, fun j : J => h1Ay (Sum.inr j), hby⟩
      simpa using h1Ay (Sum.inl i)

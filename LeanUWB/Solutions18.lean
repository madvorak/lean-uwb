import LeanUWB.Class20
import Mathlib.Algebra.Order.Sum
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.ToLin


variable {I J F : Type} [Fintype I] [Fintype J] [Field F] [LinearOrder F] [IsStrictOrderedRing F]

open scoped Matrix

-- Recommended tool:
#check Matrix.mulVecLin

/-- A system of linear equalities has a nonnegative solution if and only if
we cannot obtain a contradiction by taking a linear combination of the equalities. -/
theorem equalityFarkas (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x = b) ≠ (∃ y : I → F, 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0) := by
  convert
    fintypeFarkasBartl Aᵀ.mulVecLin ⟨⟨(b ⬝ᵥ ·), dotProduct_add b⟩, (dotProduct_smul · b)⟩
      using 1
  · constructor
    · intro ⟨x, hx, hAxb⟩
      use x
      constructor
      · exact hx
      · intro w
        simp
        show ∑ j : J, (w ᵥ* A) j * x j = b ⬝ᵥ w
        convert congr_arg (· ⬝ᵥ w) hAxb
        simp [Matrix.mulVec, Matrix.vecMul, dotProduct]
        show       ∑ j : J, (∑ i : I, w i * A i j) * x j = ∑ i : I, (∑ j : J, A i j * x j) * w i
        convert_to ∑ j : J, (∑ i : I, w i * A i j * x j) = ∑ i : I, (∑ j : J, A i j * x j * w i)
        · congr
          ext
          apply Finset.sum_mul
        · congr
          ext
          apply Finset.sum_mul
        convert_to ∑ i : I, (∑ j : J, w i * A i j * x j) = ∑ i : I, (∑ j : J, A i j * x j * w i)
        · apply Finset.sum_comm
        congr
        ext
        congr
        ext
        ring
    · intro ⟨x, hx, hAxb⟩
      use x
      constructor
      · exact hx
      · simp at hAxb
        ext i
        classical
        specialize hAxb (fun k : I => if k = i then 1 else 0)
        simp [Matrix.vecMul, dotProduct] at hAxb
        exact hAxb
  · rfl

-- Recommended tool:
#check Matrix.fromCols
-- Also consider lemmas:
#check posPart_nonneg
#check negPart_nonneg
#check Sum.nonneg_elim_iff
#check Sum.elim_comp_inl_inr

lemma basicLinearAlgebra' (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, A *ᵥ x = b) ≠ (∃ y : I → F, Aᵀ *ᵥ y = 0 ∧ b ⬝ᵥ y < 0) := by
  convert equalityFarkas (Matrix.fromCols A (-A)) b with y
  · constructor
    · intro ⟨x, hAxb⟩
      use Sum.elim x⁺ x⁻
      constructor
      · intro j
        cases j with
        | inl => simp
        | inr => simp
      simp
      convert_to A *ᵥ x⁺ + A *ᵥ -x⁻ = b
      · congr 1
        trans -(A *ᵥ x⁻)
        · exact A.neg_mulVec x⁻
        · exact (A.mulVec_neg x⁻).symm
      convert_to A *ᵥ (x⁺ + -x⁻) = b
      · exact (A.mulVec_add x⁺ (-x⁻)).symm
      convert hAxb
      convert_to x⁺ - x⁻ = x
      exact (sub_eq_add_neg x⁺ x⁻).symm
      ext
      simp
    · intro ⟨x, hx, hAxb⟩
      use (x ∘ Sum.inl) - (x ∘ Sum.inr)
      rw [Matrix.mulVec_sub]
      simp at hAxb
      convert hAxb
      rw [sub_eq_add_neg]
      congr
      rw [Matrix.neg_mulVec]
  · constructor
    · intro hAy j
      cases j with
      | inl j₁ =>
        simp [Matrix.transpose_fromCols, hAy]
      | inr j₂ =>
        simp [Matrix.transpose_fromCols]
        rw [Matrix.neg_mulVec, hAy]
        simp
    · intro hAy
      simp [Matrix.transpose_fromCols] at hAy
      apply le_antisymm
      <;> intro j
      -- The last two lines can also be replaced by these two lines:
      -- ext j
      -- apply le_antisymm
      · have hAyn := hAy (Sum.inr j)
        simp at hAyn
        rw [Matrix.neg_mulVec, ←neg_zero] at hAyn
        simp at hAyn
        exact hAyn
      · have hAyp := hAy (Sum.inl j)
        simp at hAyp
        exact hAyp

/-- A system of linear equalities has a solution if and only if
we cannot obtain a contradiction by taking a linear combination of the equalities. -/
theorem basicLinearAlgebra (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, A *ᵥ x = b) ≠ (∃ y : I → F, Aᵀ *ᵥ y = 0 ∧ b ⬝ᵥ y ≠ 0) := by
  convert basicLinearAlgebra' A b using 1
  constructor <;> intro ⟨y, hAy, hby⟩
  · rw [ne_iff_gt_or_lt] at hby
    cases hby with
    | inl h0by =>
      use -y
      constructor
      · rw [Matrix.mulVec_neg, hAy]
        exact neg_zero
      · rwa [dotProduct_neg, neg_neg_iff_pos]
    | inr hby0 =>
      use y
  · use y
    constructor
    · exact hAy
    · exact hby.ne

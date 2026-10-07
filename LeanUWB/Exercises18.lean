import LeanUWB.Class18
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
  sorry

-- Recommended tool:
#check Matrix.fromCols
-- Also consider lemmas:
#check posPart_nonneg
#check negPart_nonneg
#check Sum.nonneg_elim_iff
#check Sum.elim_comp_inl_inr

/-- A system of linear equalities has a solution if and only if
we cannot obtain a contradiction by taking a linear combination of the equalities. -/
theorem basicLinearAlgebra (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, A *ᵥ x = b) ≠ (∃ y : I → F, Aᵀ *ᵥ y = 0 ∧ b ⬝ᵥ y ≠ 0) := by
  sorry

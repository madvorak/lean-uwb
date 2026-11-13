import LeanUWB.Exercises19

open scoped Matrix

/-- Linear program where
variables are indexed by `J`,
constraints are indexed by `I`,
all coefficients are of the type `R`. -/
structure LinearProgram (I J R : Type) where
  A : Matrix I J R
  b : I → R
  c : J → R

variable {I J R : Type} [Fintype J]

/-- Is `x` a feasible solution of a linear program `P`? -/
def LinearProgram.IsFeasible [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    (P : LinearProgram I J R) (x : J → R) : Prop :=
  x ≥ 0 ∧ P.A *ᵥ x ≤ P.b

/-- Does linear program `P` reach an objective value `r`? -/
def LinearProgram.Reaches [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    (P : LinearProgram I J R) (r : R) : Prop :=
  ∃ x : J → R, P.IsFeasible x ∧ P.c ⬝ᵥ x = r

/-- To dualize a linear program, transpose the matrix and flip signs, and
exchange the RHS vector with the objective coefficients vector. -/
def LinearProgram.dualize [Ring R] (P : LinearProgram I J R) : LinearProgram J I R where
  A := -P.Aᵀ
  b := P.c
  c := P.b

theorem LinearProgram.weakDuality [Fintype I] [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
    (P : LinearProgram I J R) {p q : R} (hp : P.Reaches p) (hq : P.dualize.Reaches q) :
    p + q ≥ 0 := by
  obtain ⟨x, ⟨hx, hAxb⟩, hcx⟩ := hp
  obtain ⟨y, ⟨hy, hAyc⟩, hby⟩ := hq
  dsimp [LinearProgram.dualize] at hAyc hby
  rw [←hcx, ←hby]
  clear hcx hby p q
  have hAxy : (P.A *ᵥ x) ⬝ᵥ y ≤ P.b ⬝ᵥ y
  · exact dotProduct_le_dotProduct_of_nonneg_right hAxb hy
  have hAyx : (-P.Aᵀ *ᵥ y) ⬝ᵥ x ≤ P.c ⬝ᵥ x
  · exact dotProduct_le_dotProduct_of_nonneg_right hAyc hx
  have hAyx' : -(P.Aᵀ *ᵥ y) ⬝ᵥ x ≤ P.c ⬝ᵥ x
  · convert hAyx
    exact (P.Aᵀ.neg_mulVec y).symm
  have hAyx'' : -((P.Aᵀ *ᵥ y) ⬝ᵥ x) ≤ P.c ⬝ᵥ x
  · convert hAyx'
    exact (neg_dotProduct (P.Aᵀ *ᵥ y) x).symm
  have hAyx''' : -((P.A *ᵥ x) ⬝ᵥ y) ≤ P.c ⬝ᵥ x
  · convert hAyx''
    rw [Matrix.mulVec_transpose, ←Matrix.dotProduct_vecMul_transpose, Matrix.vecMul_transpose]
  convert add_le_add hAxy hAyx''' using 1
  · exact add_comm (P.c ⬝ᵥ x) (P.b ⬝ᵥ y)
  · exact (add_neg_cancel (P.A *ᵥ x ⬝ᵥ y)).symm

import LeanUWB.Class22

lemma or_of_neq {P Q : Prop} (hPQ : P ≠ Q) : P ∨ Q := by
  tauto

open scoped Matrix

variable {I J R : Type} [Fintype I] [Fintype J] [Field R] [LinearOrder R] [IsStrictOrderedRing R]

lemma LinearProgram.strongDuality_aux (P : LinearProgram I J R)
    (hP : ∃ x : J → R, P.IsFeasible x) (hP' : ∃ y : I → R, P.dualize.IsFeasible y) :
    ∃ p q : R, p + q ≤ 0 ∧ P.Reaches p ∧ P.dualize.Reaches q := by
  cases
    or_of_neq (
      inequalityFarkas
        (Matrix.fromRows (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ)) (Matrix.replicateRow Unit (Sum.elim P.c P.b)))
        (Sum.elim (Sum.elim P.b P.c) 0)) with
  | inl h =>
    obtain ⟨v, hv, hPv⟩ := h
    rw [←Sum.elim_comp_inl_inr v] at hv hPv
    set x : J → R := v ∘ Sum.inl
    set y : I → R := v ∘ Sum.inr
    rw [Sum.nonneg_elim_iff] at hv
    obtain ⟨hx, hy⟩ := hv
    simp [Matrix.fromBlocks_mulVec] at hPv
    obtain ⟨⟨hAx, hAy⟩, hbcxy⟩ := hPv
    specialize hbcxy ⟨⟩
    simp [Matrix.replicateRow, Matrix.mulVec] at hbcxy
    exact ⟨P.c ⬝ᵥ x, P.b ⬝ᵥ y, hbcxy , ⟨x, ⟨hx, hAx⟩, rfl⟩, ⟨y, ⟨hy, hAy⟩, rfl⟩⟩
  | inr h =>
    obtain ⟨u, hu, hPu, hbcu⟩ := h
    rw [←Sum.elim_comp_inl_inr u, ←Sum.elim_comp_inl_inr (u ∘ Sum.inl)] at hu hPu
    set y₁ : I → R := (u ∘ Sum.inl) ∘ Sum.inl
    set x₁ : J → R := (u ∘ Sum.inl) ∘ Sum.inr
    set z₁ : Unit → R := u ∘ Sum.inr
    rw [Sum.nonneg_elim_iff, Sum.nonneg_elim_iff] at hu
    obtain ⟨⟨hy₁, hx₁⟩, hz₁⟩ := hu
    simp [Matrix.transpose_fromRows, Matrix.fromBlocks_transpose, Matrix.fromBlocks_mulVec] at hPu
    set z : R := z₁ ⟨⟩
    have hPu' : 0 ≤ Sum.elim (P.Aᵀ *ᵥ y₁) (-P.A *ᵥ x₁) + Sum.elim (z₁ ⟨⟩ • P.c) (z₁ ⟨⟩ • P.b)
    · convert hPu
      ext (_|_)
      · simp [Matrix.mulVec]
        apply mul_comm
      · simp [Matrix.mulVec]
        apply mul_comm
    rw [←Sum.elim_add_add, Sum.nonneg_elim_iff] at hPu'
    obtain ⟨hAczy₁, hAbzx₁⟩ := hPu'
    sorry

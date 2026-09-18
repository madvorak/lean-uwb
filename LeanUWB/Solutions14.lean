import LeanUWB.Class14


example {T : Type} [Grupa T] (a b c : T) :
    ∃! x : T, ((a ◆ b) ◆ c) ◆ x = a := by
  obtain ⟨x, hx⟩ := Grupa.operate_inverse (b ◆ c)
  use x
  constructor
  · dsimp
    rw [←Semigrupa.assoc, ←Semigrupa.assoc, Semigrupa.assoc b, hx, Grupa.operate_neutral]
  · intro y
    dsimp
    intro hy
    obtain ⟨z, hza⟩ := Grupa.inverse_operate a
    have hy' := congr_arg (z ◆ ·) hy
    rw [Semigrupa.assoc, Semigrupa.assoc, Semigrupa.assoc, hza, Grupa.neutral_operate] at hy'
    apply right_inverse_unique
    · exact hy'
    · exact hx

theorem podmonoid_univ (T : Type) [Grupa T] : Podmonoid (⊤ : Set T) := by
  constructor
  · trivial
  intro x hx y hy
  trivial

theorem podmonoid_inter {T : Type} [Grupa T] {G₁ G₂ : Set T} (hG₁ : Podmonoid G₁) (hG₂ : Podmonoid G₂) :
    Podmonoid (G₁ ∩ G₂) := by
  constructor
  · constructor
    · exact hG₁.left
    · exact hG₂.left
  intro x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩
  constructor
  · exact hG₁.right x hx₁ y hy₁
  · exact hG₂.right x hx₂ y hy₂

theorem not_podmonoid_union :
    ∃ T : Type, ∃ _ : Grupa T, ∃ G₁ G₂ : Set T,
      (Podmonoid G₁ ∧ Podmonoid G₂) ∧ ¬(Podmonoid (G₁ ∪ G₂)) := by
  use ℤ, inferInstance
  use { 2 * n | n : ℤ }
  use { 3 * n | n : ℤ }
  constructor
  · constructor
    · exact podmonoid_nasobky 2
    · exact podmonoid_nasobky 3
  intro ⟨_, h23⟩
  specialize h23 2 (by
    left
    use 1
    exact Int.mul_one 2)
  specialize h23 3 (by
    right
    use 1
    exact Int.mul_one 3)
  cases h23 with
  | inl h2 =>
    obtain ⟨n₂, hn₂⟩ := h2
    rw [binOp_int_apply] at hn₂
    omega
  | inr h3 =>
    obtain ⟨n₃, hn₃⟩ := h3
    rw [binOp_int_apply] at hn₃
    omega

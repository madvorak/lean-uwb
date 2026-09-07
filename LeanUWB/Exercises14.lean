import LeanUWB.Class14


example {T : Type} [Grupa T] (a b c : T) :
    ∃! x : T, ((a ◆ b) ◆ c) ◆ x = a := by
  sorry

theorem podgrupa_univ (T : Type) [Grupa T] : Podgrupa (⊤ : Set T) := by
  sorry

theorem podgrupa_inter {T : Type} [Grupa T] {G₁ G₂ : Set T} (hG₁ : Podgrupa G₁) (hG₂ : Podgrupa G₂) :
    Podgrupa (G₁ ∩ G₂) := by
  sorry

theorem not_podgrupa_union :
    ∃ T : Type, ∃ _ : Grupa T, ∃ G₁ G₂ : Set T,
      (Podgrupa G₁ ∧ Podgrupa G₂) ∧ (¬ Podgrupa (G₁ ∪ G₂)) := by
  use ℤ, inferInstance
  sorry

import LeanUWB.Class14


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

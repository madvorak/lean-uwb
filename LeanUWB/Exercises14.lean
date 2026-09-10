import LeanUWB.Class14


example {T : Type} [Grupa T] (a b c : T) :
    ∃! x : T, ((a ◆ b) ◆ c) ◆ x = a := by
  sorry

theorem podmonoid_univ (T : Type) [Grupa T] : Podmonoid (⊤ : Set T) := by
  sorry

theorem podmonoid_inter {T : Type} [Grupa T] {G₁ G₂ : Set T} (hG₁ : Podmonoid G₁) (hG₂ : Podmonoid G₂) :
    Podmonoid (G₁ ∩ G₂) := by
  sorry

theorem not_podmonoid_union :
    ∃ T : Type, ∃ _ : Grupa T, ∃ G₁ G₂ : Set T,
      (Podmonoid G₁ ∧ Podmonoid G₂) ∧ ¬(Podmonoid (G₁ ∪ G₂)) := by
  use ℤ, inferInstance
  sorry

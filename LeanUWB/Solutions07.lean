import LeanUWB.Class07


example (f₁ f₂ f₃ : ℤ → ℤ) (hf₁ : Injectiv f₁) (hf₂ : Bijectiv f₂) (hf₃ : Injectiv f₃) :
    Injectiv (f₁ ∘ f₂ ∘ f₃ ∘ f₁) := by
  apply comp_injectiv
  apply comp_injectiv
  apply comp_injectiv
  exact hf₁
  exact hf₃
  exact hf₂.left
  exact hf₁

/--
Composition of surjective functions is a surjective function.
-/
theorem comp_surjectiv {A B C : Type} {f : A → B} {g : B → C} (hf : Surjectiv f) (hg : Surjectiv g) :
    Surjectiv (g ∘ f) := by
  intro c
  obtain ⟨b, hb⟩ := hg c
  obtain ⟨a, ha⟩ := hf b
  use a
  rw [←hb, ←ha]
  rfl

/--
Composition of bijective functions is a bijective function.
-/
theorem comp_bijectiv {A B C : Type} {f : A → B} {g : B → C} (hf : Bijectiv f) (hg : Bijectiv g) :
    Bijectiv (g ∘ f) := by
  obtain ⟨hf₁, hf₂⟩ := hf
  obtain ⟨hg₁, hg₂⟩ := hg
  constructor
  · apply comp_injectiv
    · exact hf₁
    · exact hg₁
  · apply comp_surjectiv
    · exact hf₂
    · exact hg₂

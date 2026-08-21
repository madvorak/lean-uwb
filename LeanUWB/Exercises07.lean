import LeanUWB.Class07


example (f₁ f₂ f₃ : ℤ → ℤ) (hf₁ : Injectiv f₁) (hf₂ : Bijectiv f₂) (hf₃ : Injectiv f₃) :
    Injectiv (f₁ ∘ f₂ ∘ f₃ ∘ f₁) := by
  sorry

/--
Composition of surjective functions is a surjective function.
-/
theorem comp_surjectiv {A B C : Type} {f : A → B} {g : B → C} (hf : Surjectiv f) (hg : Surjectiv g) :
    Surjectiv (g ∘ f) := by
  sorry

/--
Composition of bijective functions is a bijective function.
-/
theorem comp_bijectiv {A B C : Type} {f : A → B} {g : B → C} (hf : Bijectiv f) (hg : Bijectiv g) :
    Bijectiv (g ∘ f) := by
  sorry

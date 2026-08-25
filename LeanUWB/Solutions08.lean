import LeanUWB.Class08

-- Hints:
#check congr_arg
#check Function.comp_assoc

theorem left_inverse_eq_right_inverse {A B : Type} {f : A → B} {g₁ g₂ : B → A}
    (hfg : f ∘ g₁ = id) (hgf : g₂ ∘ f = id) :
    g₁ = g₂ := by
  have hg₁ : (g₂ ∘ f) ∘ g₁ = g₁
  · exact congr_arg (· ∘ g₁) hgf
  have hg₂ : g₂ ∘ (f ∘ g₁) = g₂
  · exact congr_arg (g₂ ∘ ·) hfg
  rw [←hg₁, Function.comp_assoc]
  exact hg₂

example {A B : Type} {f : A → B} {g₁ g₂ : B → A}
    (hfg : f ∘ g₁ = id) (hgf : g₂ ∘ f = id) :
    Bijectiv f := by
  rw [left_inverse_eq_right_inverse hfg hgf] at hfg
  obtain ⟨hf, -⟩ := bijectiv_and_bijectiv_of_comp_eq_id_and_comp_eq_id hfg hgf
  exact hf

import LeanUWB.Class08

-- Hints:
#check congr_arg
#check Function.comp_assoc

theorem left_inverse_eq_right_inverse {A B : Type} {f : A → B} {g₁ g₂ : B → A}
    (hfg : f ∘ g₁ = id) (hgf : g₂ ∘ f = id) :
    g₁ = g₂ := by
  calc
  _ = (g₂ ∘ f) ∘ g₁ := congr_arg (· ∘ g₁) hgf |>.symm
  _ = g₂ ∘ (f ∘ g₁) := Function.comp_assoc g₂ f g₁
  _ = g₂            := congr_arg (g₂ ∘ ·) hfg

example {A B : Type} {f : A → B} {g₁ g₂ : B → A}
    (hfg : f ∘ g₁ = id) (hgf : g₂ ∘ f = id) :
    Bijectiv f := by
  rw [left_inverse_eq_right_inverse hfg hgf] at hfg
  obtain ⟨hf, -⟩ := bijectiv_and_bijectiv_of_comp_eq_id_and_comp_eq_id hfg hgf
  exact hf

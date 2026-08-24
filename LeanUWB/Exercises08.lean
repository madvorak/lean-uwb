import LeanUWB.Class08

-- Hints:
#check congr_arg
#check Function.comp_assoc

theorem left_inverse_eq_right_inverse {A B : Type} {f : A → B} {g₁ g₂ : B → A}
    (hfg : f ∘ g₁ = id) (hgf : g₂ ∘ f = id) :
    g₁ = g₂ := by
  sorry -- TODO prove manually (without library search)

example {A B : Type} {f : A → B} {g₁ g₂ : B → A}
    (hfg : f ∘ g₁ = id) (hgf : g₂ ∘ f = id) :
    Bijectiv f := by
  sorry -- TODO prove via theorems we already proved

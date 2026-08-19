import LeanUWB.Basic

-- Allowed tactics: `exact`, `apply`, `constructor`, `left`, `right`, `intro`, `use`, `cases`, `obtain`
-- The tactic `exact` is allowed only as `exact a` where `a` is anything from the local context.

example (R : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) :
    (∃ x, ∀ y, ∀ z, ∀ b, ∃ a, R a b x y z) → (∀ z, ∀ y, ∃ x, ∀ w, ∃ v, R v w x y z) := by
  tauto -- TODO prove without `tauto`

import LeanUWB.Basic

-- Allowed tactics: `exact`, `apply`, `intro`, `constructor`, `left`, `right`, `cases`, `obtain`, `rw`, `use`, `specialize`
-- The tactic `exact` is allowed only as `exact a` where `a` is anything from the local context.

example (R : ℝ → List ℕ → Prop) (hR : ∀ a : ℝ, ∀ l : List ℕ, R a l) :
    R 5 [] := by
  tauto -- TODO prove without `tauto`

example (P Q : ℤ → Prop) (hP : ∀ x : ℤ, P x) (hQ : ∀ y : ℤ, Q y) :
    ∀ z : ℤ, P z ∧ Q z := by
  tauto -- TODO prove without `tauto`

example (P Q : ℤ → Prop) (hP : ∀ x : ℤ, P x) (hQ : ∃ y : ℤ, Q y) :
    ∃ z : ℤ, P z ∧ Q z := by
  tauto -- TODO prove without `tauto`

example (P Q : ℤ → Prop) (hPQ : ∃ z : ℤ, P z ∨ Q z) :
    (∃ x : ℤ, P x) ∨ (∃ y : ℤ, Q y) := by
  tauto -- TODO prove without `tauto`

example (P Q : ℤ → Prop) (hP : ∃ x : ℤ, P x) (hQ : ∀ y : ℤ, Q y) (h9 : ¬(Q 9)) :
    ∀ x : ℤ, P x := by
  tauto -- TODO prove without `tauto`

example (R : Char → Fin 3 → ℚ → Prop) (hR : ∀ c : Char, ∀ a : Fin 3, ∀ x : ℚ, R c a x) :
    ∀ n : Fin 3, ∀ x : ℚ, ∀ c : Char, R c n x := by
  tauto -- TODO prove without `tauto`

example (R : List ℝ → Type → Set (Fin 37) → Bool → Prop) :
    (∃ l : List ℝ, ∃ T : Type, ∃ s : Set (Fin 37), ∃ b : Bool, R l T s b) →
    (∃ s : Set (Fin 37), ∃ x : List ℝ, ∃ b : Bool, ∃ T : Type, R x T s b) := by
  tauto -- TODO prove without `tauto`

example (R : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) :
    (∃ x : ℕ, ∀ y : ℕ, ∀ z : ℕ, ∀ b : ℕ, ∃ a : ℕ, R a b x y z) →
    (∀ z : ℕ, ∀ y : ℕ, ∃ x : ℕ, ∀ w : ℕ, ∃ v : ℕ, R v w x y z) := by
  tauto -- TODO prove without `tauto`

example (P : Prop) (Q : ℕ → Prop) :
    (P → (∀ n : ℕ, Q n)) ↔ (∀ n : ℕ, P → Q n) := by
  tauto -- TODO prove without `tauto`

example (P : Prop) (Q : ℕ → Prop) :
    (P → (∃ n : ℕ, Q n)) ↔ (∃ n : ℕ, P → Q n) := by
  sorry -- TODO prove

example (P : Prop) (Q : ℕ → Prop) :
    ((∀ n : ℕ, Q n) → P) ↔ (∃ n : ℕ, Q n → P) := by
  sorry -- TODO prove

example (P : Prop) (Q : ℕ → Prop) :
    ((∃ n : ℕ, Q n) → P) ↔ (∀ n : ℕ, Q n → P) := by
  sorry -- TODO prove

example {α : Type} (A B C : Set α) : A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  sorry -- TODO prove

example {α : Type} (A B C : Set α) : A \ (B ∪ C) = (A \ B) ∩ (A \ C) := by
  sorry -- TODO prove

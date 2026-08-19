import LeanUWB.Basic

-- Allowed tactics: `exact`, `apply`, `constructor`, `left`, `right`, `intro`, `cases`, `obtain`
-- The tactic `exact` is allowed only as `exact a` where `a` is anything from the local context.

example (P Q R : Prop) : P ∧ Q ∧ R → Q ∧ P ∧ R ∧ P := by
  tauto -- TODO prove without `tauto`

example (P Q : Prop) : P → P ∨ Q := by
  tauto -- TODO prove without `tauto`

example (P Q R S : Prop) (pq : P ↔ Q) (qr : Q ↔ R) (rs : R ↔ S) : P ↔ S := by
  tauto -- TODO prove without `tauto`

example (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  tauto -- TODO prove without `tauto`

example (P : Prop) : P → ¬¬P := by
  tauto -- TODO prove without `tauto`

example (P Q : Prop) : ¬P ∧ ¬Q → ¬(P ∨ Q) := by
  tauto -- TODO prove without `tauto`

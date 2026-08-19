import LeanUWB.Basic

-- Allowed tactics: `exact`, `apply`, `intro`
-- The tactic `exact` is allowed only as `exact a` where `a` is anything from the local context.

example {P Q R : Prop} (p : P) (pq : P → Q) (pqr : P → Q → R) : R := by
  sorry

example {P Q R S : Prop} (pq : P → Q) (qr : Q → R) (rs : R → S) : P → S := by
  sorry

example {P Q R S : Prop} (pqr : P → Q → R) (qrs : (Q → R) → S) : P → S := by
  sorry

example {P Q R S T : Prop} (pq : P → Q) (qr : Q → R) (rt : R → T) (prst : (P → R) → S → T) : S → T := by
  sorry

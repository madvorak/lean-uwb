import LeanUWB.Basic

-- Allowed tactics: `exact`, `apply`, `intro`

example {P Q R : Prop} (p : P) (pq : P → Q) (pqr : P → Q → R) : R := by
  apply pqr
  exact p
  apply pq
  exact p

example {P Q R S : Prop} (pq : P → Q) (qr : Q → R) (rs : R → S) : P → S := by
  intro p
  apply rs
  apply qr
  apply pq
  exact p

example {P Q R S : Prop} (pqr : P → Q → R) (qrs : (Q → R) → S) : P → S := by
  intro p
  apply qrs
  apply pqr
  exact p

example {P Q R S T : Prop} (pq : P → Q) (qr : Q → R) (rt : R → T) (prst : (P → R) → S → T) : S → T := by
  apply prst
  intro p
  apply qr
  apply pq
  exact p

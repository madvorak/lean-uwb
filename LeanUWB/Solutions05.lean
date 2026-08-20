import LeanUWB.Basic

-- Allowed tactics: `exact`, `apply`, `intro`, `constructor`, `left`, `right`, `cases`, `obtain`, `rw`
-- The tactic `exact` is allowed only as `exact a` where `a` is anything from the local context.

example (P Q R : Prop) : P ∧ Q ∧ R → Q ∧ P ∧ R ∧ P := by
  intro ⟨p,q,r⟩
  exact ⟨q,p,r,p⟩

example (P Q : Prop) : P → P ∨ Q := by
  intro p
  left
  exact p

example (P Q R S : Prop) (pq : P ↔ Q) (qr : Q ↔ R) (rs : R ↔ S) : P ↔ S := by
  -- long proof
  obtain ⟨pq,qp⟩ := pq
  obtain ⟨qr,rq⟩ := qr
  obtain ⟨rs,sr⟩ := rs
  constructor
  · intro p
    apply rs
    apply qr
    apply pq
    exact p
  · intro s
    apply qp
    apply rq
    apply sr
    exact s

example (P Q R S : Prop) (pq : P ↔ Q) (qr : Q ↔ R) (rs : R ↔ S) : P ↔ S := by
  -- short proof
  rw [pq]
  rw [qr]
  exact rs

example (P Q R S : Prop) (pq : P ↔ Q) (qr : Q ↔ R) (rs : R ↔ S) : P ↔ S := by
  -- shortest proof
  rw [pq, qr, rs]

example (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro ⟨p,qr⟩
    cases qr with
    | inl q =>
      left
      constructor
      · exact p
      · exact q
    | inr r =>
      right
      constructor
      · exact p
      · exact r
  · intro pqpr
    cases pqpr with
    | inl pq =>
      obtain ⟨p,q⟩ := pq
      constructor
      · exact p
      · left
        exact q
    | inr pr =>
      obtain ⟨p,r⟩ := pr
      constructor
      · exact p
      · right
        exact r

example (P : Prop) : P → ¬¬P := by
  intro p np
  exact np p

example (P Q : Prop) : ¬P ∧ ¬Q → ¬(P ∨ Q) := by
  intro ⟨np,nq⟩ pq
  cases pq with
  | inl p =>
    apply np
    exact p
  | inr q =>
    apply nq
    exact q

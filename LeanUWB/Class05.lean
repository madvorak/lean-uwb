import LeanUWB.Basic


-- ## AND

example {P Q : Prop} (pq : P ∧ Q) : Q ∧ P := by
  obtain ⟨p,q⟩ := pq
  constructor
  · exact q
  · exact p

example {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro pq
  obtain ⟨p,q⟩ := pq
  constructor
  · exact q
  · exact p

example {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro ⟨p,q⟩
  constructor
  · exact q
  · exact p

example {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro ⟨p,q⟩
  exact ⟨q,p⟩

example {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro pq
  exact And.symm pq

example {P Q : Prop} : P ∧ Q → Q ∧ P := by
  exact And.symm

example {P Q : Prop} : P ∧ Q → Q ∧ P :=
  And.symm

example {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro ⟨p,q⟩
    exact ⟨q,p⟩
  · intro ⟨q,p⟩
    exact ⟨p,q⟩

example {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro pq
    exact And.symm pq
  · intro pq
    exact And.symm pq

example {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor
  · apply And.symm
  · apply And.symm

example {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor <;> apply And.symm

example {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  tauto

example {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  And.comm


-- ## OR

example {P Q : Prop} (pq : P ∨ Q) : Q ∨ P := by
  cases pq with
  | inl p =>
    right
    exact p
  | inr q =>
    left
    exact q

example {P Q : Prop} (pq : P ∨ Q) : Q ∨ P := by
  exact Or.symm pq

example {P Q : Prop} : P ∨ Q → Q ∨ P :=
  Or.symm

example {P Q : Prop} : P ∨ Q ↔ Q ∨ P := by
  tauto

example {P Q : Prop} : P ∨ Q ↔ Q ∨ P :=
  Or.comm


-- ## NOT

theorem one_add_one_ne_three : 1 + 1 ≠ 3 := by norm_num

example : ¬(1 + 1 = 3) := one_add_one_ne_three

example : (1 + 1 = 3) → False := one_add_one_ne_three

example (n : ℕ) (h1 : n = 1) (h3 : n = 3) : n = 5 := by
  have hn : n = 2 * n - n
  · omega
  nth_rw 1 [hn, h3, h1]

example (n : ℕ) (h1 : n = 1) (h3 : n = 3) : n = 5 := by
  exfalso
  rw [h1] at h3
  norm_num at h3

theorem impossible_equivalence {P : Prop} : (P ↔ ¬ P) → False := by
  intro hyp
  if p : P
  then
    have np : ¬ P
    · rw [hyp] at p
      exact p
    exact np p
  else
    apply p
    rw [hyp]
    exact p

example {P : Prop} : (P ↔ ¬ P) → False := by
  tauto

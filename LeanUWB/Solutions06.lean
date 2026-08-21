import LeanUWB.Basic

-- Allowed tactics: `exact`, `apply`, `intro`, `constructor`, `left`, `right`, `cases`, `obtain`, `rw`, `use`, `specialize`, `if`
-- The tactic `exact` is allowed only as `exact a` where `a` is anything from the local context.

example (R : ℝ → List ℕ → Prop) (hR : ∀ a : ℝ, ∀ l : List ℕ, R a l) :
    R 5 [] := by
  apply hR

example (P Q : ℤ → Prop) (hP : ∀ x : ℤ, P x) (hQ : ∀ y : ℤ, Q y) :
    ∀ z : ℤ, P z ∧ Q z := by
  intro z
  constructor
  · apply hP
  · apply hQ

example (P Q : ℤ → Prop) (hP : ∀ x : ℤ, P x) (hQ : ∃ y : ℤ, Q y) :
    ∃ z : ℤ, P z ∧ Q z := by
  obtain ⟨y, hy⟩ := hQ
  use y
  constructor
  · apply hP
  · exact hy

example (P Q : ℤ → Prop) (hPQ : ∃ z : ℤ, P z ∨ Q z) :
    (∃ x : ℤ, P x) ∨ (∃ y : ℤ, Q y) := by
  obtain ⟨z, hz⟩ := hPQ
  cases hz with
  | inl hPz =>
    left
    use z
  | inr hQz =>
    right
    use z

example (P Q : ℤ → Prop) (hP : ∃ x : ℤ, P x) (hQ : ∀ y : ℤ, Q y) (h9 : ¬(Q 9)) :
    ∀ x : ℤ, P x := by
  exfalso
  apply h9
  apply hQ

example (R : Char → Fin 3 → ℚ → Prop) (hR : ∀ c : Char, ∀ a : Fin 3, ∀ x : ℚ, R c a x) :
    ∀ n : Fin 3, ∀ x : ℚ, ∀ c : Char, R c n x := by
  intro n x c
  apply hR

example (R : List ℝ → Type → Set (Fin 37) → Bool → Prop) :
    (∃ l : List ℝ, ∃ T : Type, ∃ s : Set (Fin 37), ∃ b : Bool, R l T s b) →
    (∃ s : Set (Fin 37), ∃ x : List ℝ, ∃ b : Bool, ∃ T : Type, R x T s b) := by
  intro ⟨l, T, s, b, hlTsb⟩
  use s, l, b, T

example (R : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) :
    (∃ x : ℕ, ∀ y : ℕ, ∀ z : ℕ, ∀ b : ℕ, ∃ a : ℕ, R a b x y z) →
    (∀ z : ℕ, ∀ y : ℕ, ∃ x : ℕ, ∀ w : ℕ, ∃ v : ℕ, R v w x y z) := by
  intro ⟨x, hx⟩ z y
  use x
  intro w
  apply hx

example (P : Prop) (Q : ℕ → Prop) :
    (P → (∀ n : ℕ, Q n)) ↔ (∀ n : ℕ, P → Q n) := by
  constructor
  · intro hPQ n p
    apply hPQ
    exact p
  · intro hPQ p n
    apply hPQ
    exact p

example (P : Prop) (Q : ℕ → Prop) :
    (P → (∃ n : ℕ, Q n)) ↔ (∃ n : ℕ, P → Q n) := by
  constructor
  · intro hPQ
    if hp : P then
      specialize hPQ hp
      obtain ⟨n, hn⟩ := hPQ
      use n
      intro
      exact hn
    else
      use 0
      intro p
      exfalso
      apply hp
      exact p
  · intro ⟨n, hn⟩ p
    specialize hn p
    use n

example (P : Prop) (Q : ℕ → Prop) :
    ((∀ n : ℕ, Q n) → P) ↔ (∃ n : ℕ, Q n → P) := by
  constructor
  · intro hQP
    if hQ : ∀ n : ℕ, Q n then
      specialize hQP hQ
      use 0
      intro
      exact hQP
    else
      push Not at hQ
      obtain ⟨n, hn⟩ := hQ
      use n
      intro hQn
      exfalso
      apply hn
      exact hQn
  · intro ⟨n, hn⟩ hQ
    apply hn
    apply hQ

example (P : Prop) (Q : ℕ → Prop) :
    ((∃ n : ℕ, Q n) → P) ↔ (∀ n : ℕ, Q n → P) := by
  constructor
  · intro hQP n hQn
    apply hQP
    use n
  · intro hQP ⟨n, hn⟩
    exact hQP n hn

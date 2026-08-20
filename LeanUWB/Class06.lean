import LeanUWB.Basic


example : ∀ n : ℕ, n * 3 = n + n + n := by
  intro x
  ring

example : ∃ n : ℕ, 2 ^ n = 512 := by
  use 9
  norm_num

theorem real_dense (x z : ℝ) (hxz : x < z) : ∃ y : ℝ, x < y ∧ y < z := by
  use (x + z) / 2
  constructor
  · convert_to x / 2 + x / 2 < x / 2 + z / 2
    · ring
    · rw [add_div]
    · apply add_lt_add_right
      rw [div_lt_div_iff_of_pos_right]
      · exact hxz
      · exact zero_lt_two
  · convert_to x / 2 + z / 2 < z / 2 + z / 2
    · rw [add_div]
    · ring
    · apply add_lt_add_left
      rw [div_lt_div_iff_of_pos_right]
      · exact hxz
      · exact zero_lt_two

theorem rat_dense : ∀ x z : ℚ, x < z → ∃ y : ℚ, x < y ∧ y < z := by
  intro x z hxz
  use (x + z) / 2
  grind

theorem int_not_dense : ¬(∀ x z : ℤ, x < z → ∃ y : ℤ, x < y ∧ y < z) := by
  push Not
  use 3, 4
  grind

theorem deMorgan_ex {α : Type} {R : α → Prop} (hR : ∃ a : α, R a) : ¬(∀ a : α, ¬ R a) := by
  obtain ⟨a, ha⟩ := hR
  intro hR'
  apply hR'
  exact ha

example {α : Type} {R : α → Prop} (hR : ∃ a : α, R a) : ¬(∀ a : α, ¬ R a) := by
  obtain ⟨a, ha⟩ := hR
  push Not
  use a

example {α : Type} {R : α → Prop} (hR : ∃ a : α, R a) : ¬(∀ a : α, ¬ R a) := by
  tauto

example {α : Type} {R : α → Prop} (hR : ∃ a : α, R a) : ¬(∀ a : α, ¬ R a) :=
  Exists.classicalRecOn hR

example (A : ℕ × ℝ → Prop) (hA : ∃ x : ℕ × ℝ, A x) : ¬(∀ p : ℕ × ℝ, ¬ A p) :=
  deMorgan_ex hA

example (S : Set ℤ) (hS : ∃ e : ℤ, e ∈ S) : ¬(∀ a : ℤ, a ∉ S) :=
  deMorgan_ex hS

example (T : Set (Set ℤ × Set (Set (Set ℝ)) → Set (Set ℕ → Set ℚ))) (hT : ∃ t, t ∈ T) : ¬(∀ t, t ∉ T) :=
  deMorgan_ex hT

example : { x : ℤ | x ≥ 100 } ⊆ { y : ℤ | y > 3 } := by
  intro a ha
  simp at *
  linarith

example (M : Set ℝ) : ∀ a ∈ M, a ≤ |a| := by
  intro a _
  exact le_abs_self a

example {α : Type} (A B C : Set α) : A ∩ B ∩ C ⊆ B := by
  intro x hx
  obtain ⟨⟨hA, hB⟩, hC⟩ := hx
  exact hB

example {α : Type} (A B C : Set α) : A ∩ B ∩ C ⊆ B := by
  trans A ∩ B
  · apply Set.inter_subset_left
  · apply Set.inter_subset_right

example {α : Type} (A B C : Set α) : A ∩ B ∩ C ⊆ B := by
  grind

import LeanUWB.Basic


def lim (s : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - l| < ε

theorem lim_add (u v : ℕ → ℝ) (a b : ℝ)
    (ha : lim u a) (hb : lim v b) :
    lim (u + v) (a + b) := by
  intro ε hε
  specialize ha (ε / 2) (half_pos hε)
  specialize hb (ε / 2) (half_pos hε)
  obtain ⟨Nᵤ, hu⟩ := ha
  obtain ⟨Nᵥ, hv⟩ := hb
  use max Nᵤ Nᵥ
  intro n hn
  -- specialize hu n (le_of_max_le_left hn)
  -- specialize hv n (le_of_max_le_right hn)
  -- calc |(u n + v n) - (a + b)|
  --    = |(u n - a) + (v n - b)| := by grind
  -- _  ≤ |u n - a|  + |v n - b| := by grind
  -- _  < ε := by grind
  show |(u n + v n) - (a + b)| < ε
  grind

example (u v w : ℕ → ℝ) (a b c : ℝ)
    (ha : lim u a) (hb : lim v b) (hc : lim w c) :
    lim (u + v + w) (a + b + c) := by
  apply lim_add
  apply lim_add
  exact ha
  exact hb
  exact hc

theorem lim_sub (u v : ℕ → ℝ) (a b : ℝ)
    (ha : lim u a) (hb : lim v b) :
    lim (u - v) (a - b) := by
  convert lim_add u (-v) a (-b) ha (by
    intro ε hε
    specialize hb ε hε
    obtain ⟨N, hN⟩ := hb
    use N
    intro n hn
    specialize hN n hn
    rw [abs_sub_comm]
    simp
    rw [add_comm]
    exact hN)
  · exact sub_eq_add_neg u v
  · exact sub_eq_add_neg a b

example (u v w : ℕ → ℝ) (a b c : ℝ)
    (ha : lim u a) (hb : lim v b) (hc : lim w c) :
    lim (u + 3*v - w) (a + 3*b - c) := by
  convert_to lim (u + v + v + v - w) (a + b + b + b - c)
  · ring
  · ring
  apply lim_sub
  apply lim_add
  apply lim_add
  apply lim_add
  exact ha
  exact hb
  exact hb
  exact hb
  exact hc

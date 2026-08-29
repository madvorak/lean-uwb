import LeanUWB.Basic


def lim (s : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - l| < ε

theorem lim_add (u v : ℕ → ℝ) (a b : ℝ)
    (ha : lim u a) (hb : lim v b) :
    lim (u + v) (a + b) := by
  sorry

example (u v w : ℕ → ℝ) (a b c : ℝ)
    (ha : lim u a) (hb : lim v b) (hc : lim w c) :
    lim (u + v + w) (a + b + c) := by
  sorry

theorem lim_sub (u v : ℕ → ℝ) (a b : ℝ)
    (ha : lim u a) (hb : lim v b) :
    lim (u - v) (a - b) := by
  sorry

example (u v w : ℕ → ℝ) (a b c : ℝ)
    (ha : lim u a) (hb : lim v b) (hc : lim w c) :
    lim (u + 3*v - w) (a + 3*b - c) := by
  sorry

import LeanUWB.Class03


example (a : ℚ) : a ^ 2 = a * a := by
  -- Prove by finding a term.
  sorry

example (a b c d : ℕ) (ha : a = b + d) (hb : b = a * a) (hc : c = b + d) (hd : d = c * c) :
    b ^ d = d ^ b := by
  -- Prove using only `rw`.
  sorry

example (a b c d : ℤ) (ha : a = d ^ 4) (hb : b = 1 / c) (hc : c = a - b) (hd : d = 4 * a) :
    (a + b) ^ 2 - c ^ 2 = b * d := by
  -- Prove using only `rw` and `ring`.
  sorry

example (x : ℝ) : 50*x^2 - 126*x + 96 ≥ 0 := by
  sorry

example (x y : ℝ) : 2 * x^3 * y^3 ≤ x^4 * y^2 + x^2 * y^4 := by
  sorry

example (x y z : ℝ) : 4*x^2 + 12*x*y - 4*x*z + 9*y^2 - 6*y*z + z^2 ≥ 0 := by
  sorry

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / a + 1 / b ≤ a / b^2 + b / a^2 := by
  sorry

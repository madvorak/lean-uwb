import LeanUWB.Class03


example (a : ℚ) : a ^ 2 = a * a :=
  pow_two a

example (a b c d : ℕ) (ha : a = b + d) (hb : b = a * a) (hc : c = b + d) (hd : d = c * c) :
    b ^ d = d ^ b := by
  rw [←ha] at hc
  rw [hc] at hd
  rw [←hd] at hb
  rw [hb]

example (a b c d : ℤ) (ha : a = d ^ 4) (hb : b = 1 / c) (hc : c = a - b) (hd : d = 4 * a) :
    (a + b) ^ 2 - c ^ 2 = b * d := by
  rw [hd, hc]
  ring

example (x : ℝ) : 50*x^2 - 126*x + 96 ≥ 0 := by
  have : 49*x^2 - 126*x + 81 ≥ 0
  · convert_to (7*x - 9) ^ 2 ≥ 0
    · ring
    exact sq_nonneg (7*x - 9)
  nlinarith

example (x y : ℝ) : 2 * x^3 * y^3 ≤ x^4 * y^2 + x^2 * y^4 := by
  have : 0 ≤ x^4 * y^2 + x^2 * y^4 - 2 * x^3 * y^3
  · convert_to 0 ≤ (x^2*y - x*y^2) ^ 2
    · ring
    exact sq_nonneg (x^2*y - x*y^2)
  linarith

example (x y z : ℝ) : 4*x^2 + 12*x*y - 4*x*z + 9*y^2 - 6*y*z + z^2 ≥ 0 := by
  convert_to (2*x + 3*y - z) ^ 2 ≥ 0
  · ring
  exact sq_nonneg (2*x + 3*y - z)

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / a + 1 / b ≤ a / b^2 + b / a^2 := by
  have : 0 ≤ a^3 + b^3 - a*b^2 - a^2*b
  · convert_to 0 ≤ (a - b) ^ 2 * (a + b)
    · ring
    nlinarith
  have : a*b^2 + a^2*b ≤ a^3 + b^3
  · linarith
  have : (a*b^2 + a^2*b) / (a^2 * b^2) ≤ (a^3 + b^3) / (a^2 * b^2)
  · have h0 : 0 < a^2 * b^2
    · positivity
    exact (div_le_div_iff_of_pos_right h0).← this
  convert this <;> grind

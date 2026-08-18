import LeanUWB.Basic


-- ## Equalities

example (n : ℕ) : 2 * n = n + n := two_mul n

example (n : ℕ) : 2 * n = n + n := by
  ring

example (x y : ℤ) : (x + y) ^ 2 = x^2 + 2*x*y + y^2 := by
  ring

example (x y : ℚ) : (x - y) ^ 3 = x^3 - 3*x^2*y + 3*x*y^2 - y^3 := by
  ring

example (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  ring

example (n : ℕ) : 2 ^ (n+3) = 8 * 2^n := by
  ring

example (n : ℕ) (hn : n = 5) : n - 1 = 4 := by
  rw [hn]

example (n : ℕ) (hn : 5 = n) : n - 1 = 4 := by
  rw [Eq.symm hn]

example (n : ℕ) (hn : 5 = n) : n - 1 = 4 := by
  rw [←hn]

example (a b c : ℝ) (ha : a = 2) (hb : b = 3) (hc : c = 5) : a + b = c := by
  rw [ha, hb, hc]
  norm_num

example (a : ℝ) (h2 : a = 2) (h3 : a = 3) : False := by
  rw [h2] at h3
  norm_num at h3

example (x : ℝ) (hx : x ≠ 0) : x^2 / x = x := by
  field_simp

example (x : ℝ) (hx : x ≠ 0) : x + 1/x = (x^2 + 1) / x := by
  field_simp

example (x y z : ℝ) (hx : x ≠ 0) : x*y*z + 3*y*z*x - 2*z*x*y = y*x*z + x^2*z*y/x := by
  field_simp
  norm_num


-- ## Inequalities

example (x y z : ℝ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := hxy.trans hyz

example (x y z : ℝ) (hxy : x < y) (hyz : y < z) : x < z := hxy.trans hyz

example (x y z : ℝ) (hxy : x < y) (hyz : y ≤ z) : x < z := hxy.trans_le hyz

example (x y z : ℝ) (hxy : x ≤ y) (hyz : y < z) : x < z := hxy.trans_lt hyz

example (a b c d : ℝ) (habcd : a + b + c ≤ 2 * d) (hab : a ≤ b) (hac : 2 * a ≤ c) : 2 * a ≤ d := by
  linarith

example (x y : ℝ) (hxy : x ≤ y) : x ≤ y + y*y := by
  nlinarith

example (x y : ℝ) (hx : x < 0) (hy : y < 0) : x * 7 * y > 0 := by
  nlinarith

example (x y : ℝ) : x*x - 2*x*y + y*y ≥ 0 := by
  convert_to (x - y) ^ 2 ≥ 0
  ring
  exact sq_nonneg (x - y)

example (x : ℝ) : 16*x^4 - 96*x^3 + 216*x^2 - 216*x + 81 ≥ 0 := by
  convert_to ((2*x - 3) ^ 2) ^ 2 ≥ 0
  ring
  exact sq_nonneg ((2*x - 3) ^ 2)

example (x : ℝ) : 16*x^4 - 96*x^3 + 216*x^2 - 216*x + 100 ≥ 0 := by
  have : 16*x^4 - 96*x^3 + 216*x^2 - 216*x + 81 ≥ 0
  · convert_to ((2*x - 3) ^ 2) ^ 2 ≥ 0
    · ring
    exact sq_nonneg ((2*x - 3) ^ 2)
  linarith

example (x : ℝ) : 16*x^4 - 96*x^3 + 216*x^2 - 216*x + 100 ≥ 0 := by
  convert_to ((2*x - 3) ^ 2) ^ 2 + 19 ≥ 0
  ring
  nlinarith

example (x : ℝ) (hx : x > 0) : x + 1/x ≥ 2 := by
  have : (x - 1) ^ 2 ≥ 0
  · exact sq_nonneg (x - 1)
  have : x*x + 1 - 2*x ≥ 0
  · grind
  have : x*x + 1 ≥ 2*x
  · exact le_of_sub_nonneg this
  have : (x*x + 1) / x ≥ 2*x / x
  · exact (div_le_div_iff_of_pos_right hx).← this
  convert_to x*x/x + 1/x ≥ 2*x/x
  <;> grind

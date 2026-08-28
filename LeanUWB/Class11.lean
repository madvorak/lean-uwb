import LeanUWB.Class02


theorem sum_append (x y : List ℕ) : sum (x ++ y) = sum x + sum y := by
  induction x with
  | nil =>
    simp [sum]
  | cons d l ih =>
    simp [sum]
    rw [ih]
    exact Eq.symm (Nat.add_assoc d (sum l) (sum y))


lemma pow_two_lt_two_pow_aux (n : ℕ) : (n+5) ^ 2 < 2 ^ (n+5) := by
  induction n with
  | zero =>
    norm_num
  | succ m ih =>
    convert_to (m+6) ^ 2 < 2 ^ (m+5) * 2
    · ring
    have : 3 * (m+5) < 2 ^ (m+5)
    · nlinarith
    linarith

theorem pow_two_lt_two_pow (n : ℕ) (hn : n > 4) : n ^ 2 < 2 ^ n := by
  have h5 : n = n - 5 + 5
  · exact (Nat.sub_eq_iff_eq_add hn).→ rfl
  rw [h5]
  exact pow_two_lt_two_pow_aux (n - 5)

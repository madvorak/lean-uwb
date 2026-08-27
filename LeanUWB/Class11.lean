import LeanUWB.Class01
import LeanUWB.Class02
import Mathlib.Analysis.SpecialFunctions.Sqrt


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


lemma formulaBinet_aux {x : ℝ} (hx : x * x = x + 1) (m : ℕ) :
    x ^ (m+1) = x * fibonacci (m+1) + fibonacci m := by
  induction m with
  | zero =>
    simp [fibonacci]
  | succ n ih =>
    convert_to x * x ^ (n+1) = x * (fibonacci n + fibonacci (n+1)) + fibonacci (n+1)
    · ring
    · simp [fibonacci]
    rw [ih]
    convert_to (x * x) * fibonacci (n+1) + x * fibonacci n = x * (fibonacci n + fibonacci (n+1)) + fibonacci (n+1)
    · ring
    rw [hx]
    ring

theorem formulaBinet (n : ℕ) :
    fibonacci n = (1 / √5) * (((1 + √5) / 2) ^ n - ((1 - √5) / 2) ^ n) := by
  cases n with
  | zero =>
    simp [fibonacci]
  | succ m =>
    have h5 : √5 * √5 = 5
    · have h0 : 0 ≤ (5 : ℝ)
      · norm_num
      exact Real.mul_self_sqrt h0
    rw [formulaBinet_aux, formulaBinet_aux]
    · ring_nf
      convert_to (fibonacci (m + 1) : ℝ) = (1 : ℝ) * (fibonacci (1 + m))
      · rw [add_comm]
      · rw [CommGroupWithZero.mul_inv_cancel]
        norm_num
      convert_to (fibonacci (m + 1) : ℝ) = (fibonacci (m + 1) : ℝ)
      · ring_nf
      rfl
    · have h2 :
          ((1 - √5) / 2) * ((1 - √5) / 2) =
          (1 - 2 * √5 + √5 * √5) / 2 / 2
      · ring
      rw [h2, h5]
      ring
    · have h2 :
          ((1 + √5) / 2) * ((1 + √5) / 2) =
          (1 + 2 * √5 + √5 * √5) / 2 / 2
      · ring
      rw [h2, h5]
      ring

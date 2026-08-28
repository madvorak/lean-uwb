import LeanUWB.Basic
import Mathlib.Data.Nat.Prime.Basic


theorem strong_induction {P : ℕ → Prop} (hP : ∀ m : ℕ, (∀ k : ℕ, k < m → P k) → P m) :
    ∀ n : ℕ, P n := by
  sorry -- TODO prove manually (without library search)


-- Hints for the next proof:
#check Nat.exists_dvd_of_not_prime
#check Nat.le_of_dvd
#check Nat.dvd_trans

theorem exists_prime_divisor : ∀ n : ℕ, 2 ≤ n → ∃ p : ℕ, p.Prime ∧ p ∣ n := by
  sorry -- TODO prove

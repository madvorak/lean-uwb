import LeanUWB.Basic
import Mathlib.Data.Nat.Prime.Basic


theorem strong_induction {P : ℕ → Prop} (hP : ∀ m : ℕ, (∀ k : ℕ, k < m → P k) → P m) :
    ∀ n : ℕ, P n := by
  have hP' : ∀ N : ℕ, ∀ n < N, P n
  · intro N
    induction N with
    | zero =>
      intro n hn
      exfalso
      simp at hn
    | succ M ih =>
      intro n hn
      apply hP
      intro k hk
      apply ih
      omega
  intro n
  apply hP' (n+1)
  exact Nat.lt_add_one n

theorem exists_prime_divisor : ∀ n : ℕ, 2 ≤ n → ∃ p : ℕ, p.Prime ∧ p ∣ n := by
  apply strong_induction
  intro m IH h2
  if hm : m.Prime then
    use m
  else
    obtain ⟨d, hdm, hd1, hdm'⟩ := Nat.exists_dvd_of_not_prime h2 hm
    obtain ⟨p, hp, hpd⟩ := IH d (by
      have h0 : 0 < m
      · exact Nat.zero_lt_of_lt h2
      have hdm'' : d ≤ m
      · exact Nat.le_of_dvd h0 hdm
      exact Nat.lt_of_le_of_ne hdm'' hdm'
    ) (by
      have h0 : 0 ≠ d
      · aesop
      omega)
    use p
    constructor
    · exact hp
    · exact Nat.dvd_trans hpd hdm

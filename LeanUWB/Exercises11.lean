import LeanUWB.Class11

-- Hint: try writing `dsimp [foo]` instead of `unfold foo`

theorem rever_rever {T : Type} (x : List T) : rever (rever x) = x := by
  sorry

theorem sum_oddListIncr (n : ℕ) : sum (oddListIncr n) = n * n := by
  sorry

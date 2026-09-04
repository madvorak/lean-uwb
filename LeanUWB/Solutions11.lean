import LeanUWB.Class11

-- Hint: try writing `dsimp [foo]` instead of `unfold foo`

lemma rever_append {T : Type} (x y : List T) : rever (x ++ y) = rever y ++ rever x := by
  induction x with
  | nil =>
    simp [rever]
  | cons d l ih =>
    dsimp [rever]
    rw [ih]
    exact List.append_assoc (rever y) (rever l) [d]

theorem rever_rever {T : Type} (x : List T) : rever (rever x) = x := by
  induction x with
  | nil =>
    rfl
  | cons d l ih =>
    dsimp [rever]
    rw [rever_append, ih]
    rfl


lemma sum_oddList (n : ℕ) : sum (oddList n) = n * n := by
  induction n with
  | zero =>
    rfl
  | succ m ih =>
    dsimp [sum, oddList]
    rw [ih]
    ring

lemma sum_rever (x : List ℕ) : sum (rever x) = sum x := by
  induction x with
  | nil =>
    rfl
  | cons d l ih =>
    dsimp [rever, sum]
    rw [sum_append, ih]
    exact add_comm (sum l) (sum [d])

theorem sum_oddListIncr (n : ℕ) : sum (oddListIncr n) = n * n := by
  dsimp [oddListIncr]
  rw [sum_rever]
  apply sum_oddList

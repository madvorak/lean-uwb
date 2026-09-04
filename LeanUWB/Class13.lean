import LeanUWB.Class02


lemma reversAppend_eq_rever {T : Type} (x y : List T) :
    reversAppend x y = rever y ++ x := by
  induction y generalizing x with
  | nil =>
    rfl
  | cons d l ih =>
    simp [rever, reversAppend]
    apply ih

theorem revers_eq_rever (T : Type) : @revers T = @rever T := by
  ext1 l
  unfold revers
  rw [reversAppend_eq_rever]
  apply List.append_nil

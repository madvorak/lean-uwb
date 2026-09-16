import LeanUWB.Class15

variable {A : Type} [CompleteLattic A]

noncomputable instance : Bot A where
  bot := ⊓ Set.univ

noncomputable instance : Top A where
  top := ⊔ Set.univ

theorem JoinContinuous.constructLeastFixpoint {F : A → A} (hF : JoinContinuous F) :
    LeastFixpoint F (⊔ { F^[i] ⊥ | i : ℕ }) := by
  sorry

theorem MeetContinuous.constructGreatFixpoint {F : A → A} (hF : MeetContinuous F) :
    GreatFixpoint F (⊓ { F^[i] ⊤ | i : ℕ }) := by
  sorry

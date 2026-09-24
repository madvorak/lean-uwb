import LeanUWB.Class15

variable {A : Type} [CompleteLattic A]

noncomputable instance : Bot A where
  bot := ⊓ Set.univ

noncomputable instance : Top A where
  top := ⊔ Set.univ

lemma bot_under (x : A) : ⊥ ⊑ x := by
  sorry

lemma top_above (x : A) : x ⊑ ⊤ := by
  sorry

lemma above_iff_supre_pair (a b : A) :
    a ⊑ b ↔ ⊔ {a, b} = b := by
  sorry

lemma under_iff_infim_pair (a b : A) :
    a ⊑ b ↔ ⊓ {a, b} = a := by
  sorry

lemma JoinContinuous.monoton {F : A → A} (hF : JoinContinuous F) :
    Monoton F := by
  sorry

lemma MeetContinuous.monoton {F : A → A} (hF : MeetContinuous F) :
    Monoton F := by
  sorry

theorem JoinContinuous.constructLeastFixpoint {F : A → A} (hF : JoinContinuous F) :
    LeastFixpoint F (⊔ { F^[i] ⊥ | i : ℕ }) := by
  sorry

theorem MeetContinuous.constructGreatFixpoint {F : A → A} (hF : MeetContinuous F) :
    GreatFixpoint F (⊓ { F^[i] ⊤ | i : ℕ }) := by
  sorry

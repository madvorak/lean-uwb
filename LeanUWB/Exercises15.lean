import LeanUWB.Class15


example {A : Type} [Poset A] (a b c : A) :
    -- There is no directed triange in a poset.
    (a ⊑ b ∧ b ⊑ c ∧ c ⊑ a) → a = b := by
  sorry


theorem greatFixpoint_supre_prefixpoint {A : Type} {F : A → A} [CompleteLattic A] (hF : Monoton F) :
    -- The least upper bound of all prefixpoints is a great fixpoint.
    GreatFixpoint F (⊔ Prefixpoint F) := by
  sorry

theorem leastFixpoint_infim_posfixpoint {A : Type} {F : A → A} [CompleteLattic A] (hF : Monoton F) :
    -- The great lower bound of all posfixpoints is a least fixpoint.
    LeastFixpoint F (⊓ Posfixpoint F) := by
  sorry

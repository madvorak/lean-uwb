import LeanUWB.Class15


example {A : Type} [Poset A] (a b c : A) :
    -- There is no directed triange in a poset.
    (a ⊑ b ∧ b ⊑ c ∧ c ⊑ a) → a = b := by
  sorry


instance (α : Type) : Relation (Set α) :=
  ⟨(· ⊆ ·)⟩

instance (α : Type) : Poset (Set α) := by
  constructor
  · intro x
    exact Set.Subset.refl x
  · intro x y ⟨hxy, hyx⟩
    exact Set.Subset.antisymm hxy hyx
  · intro x y z ⟨hxy, hyz⟩
    exact Set.Subset.trans hxy hyz

instance (α : Type) : CompleteLattic (Set α) := by
  sorry


theorem greatFixpoint_supre_prefixpoint {A : Type} {F : A → A} [CompleteLattic A] (hF : Monoton F) :
    -- The least upper bound of all prefixpoints is a great fixpoint.
    GreatFixpoint F (⊔ Prefixpoint F) := by
  sorry

theorem leastFixpoint_infim_posfixpoint {A : Type} {F : A → A} [CompleteLattic A] (hF : Monoton F) :
    -- The great lower bound of all posfixpoints is a least fixpoint.
    LeastFixpoint F (⊓ Posfixpoint F) := by
  sorry

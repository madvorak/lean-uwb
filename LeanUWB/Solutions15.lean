import LeanUWB.Class15


example {A : Type} [Poset A] (a b c : A) :
    -- There is no directed triange in a poset.
    (a ⊑ b ∧ b ⊑ c ∧ c ⊑ a) → a = b := by
  intro ⟨hab, hbc, hca⟩
  apply Poset.antis
  constructor
  · exact hab
  · apply Poset.trans
    constructor
    · exact hbc
    · exact hca


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
  constructor
  · intro S
    use { a : α | ∃ x ∈ S, a ∈ x }
    constructor
    · intro s hsS a has
      dsimp
      use s
    · intro s hSs a haS
      dsimp at haS
      obtain ⟨x, hxS, hax⟩ := haS
      specialize hSs x hxS
      apply hSs
      exact hax
  · intro S
    use { a : α | ∀ x ∈ S, a ∈ x }
    constructor
    · intro s hsS a haS
      dsimp at haS
      apply haS
      exact hsS
    · intro s hSs a has x hxS
      specialize hSs x hxS
      apply hSs
      exact has


theorem greatFixpoint_supre_prefixpoint {A : Type} {F : A → A} [CompleteLattic A] (hF : Monoton F) :
    -- The least upper bound of all prefixpoints is a great fixpoint.
    GreatFixpoint F (⊔ Prefixpoint F) := by
  have hyF := supre_is_upper (Prefixpoint F)
  have hFy := supre_is_least (Prefixpoint F)
  set y := ⊔ Prefixpoint F
  have hyFy : y ⊑ F y
  · have hFxFy : ∀ x : A, Prefixpoint F x → F x ⊑ F y
    · intro x hx
      apply hF
      apply hyF
      exact hx
    have hxFy : ∀ x : A, Prefixpoint F x → x ⊑ F y
    · intro x hx
      apply Poset.trans
      constructor
      · exact hx
      · apply hFxFy
        exact hx
    apply hFy
    exact hxFy
  constructor
  · apply Poset.antis
    constructor
    · apply hyF
      apply hF
      exact hyFy
    · exact hyFy
  · intro a ha
    apply hyF
    apply prefixpoint_of_fixpoint
    exact ha

theorem leastFixpoint_infim_posfixpoint {A : Type} {F : A → A} [CompleteLattic A] (hF : Monoton F) :
    -- The great lower bound of all posfixpoints is a least fixpoint.
    LeastFixpoint F (⊓ Posfixpoint F) := by
  have hbF := infim_is_lower (Posfixpoint F)
  have hFb := infim_is_great (Posfixpoint F)
  set b := ⊓ Posfixpoint F
  have hFbb : F b ⊑ b
  · have hFbFx : ∀ x : A, Posfixpoint F x → F b ⊑ F x
    · intro x hx
      apply hF
      apply hbF
      exact hx
    have hFbx : ∀ x : A, Posfixpoint F x → F b ⊑ x
    · intro x hx
      apply Poset.trans
      constructor
      · apply hFbFx
        exact hx
      · exact hx
    apply hFb
    exact hFbx
  constructor
  · apply Poset.antis
    constructor
    · exact hFbb
    · apply hbF
      apply hF
      exact hFbb
  · intro a ha
    apply hbF
    apply posfixpoint_of_fixpoint
    exact ha

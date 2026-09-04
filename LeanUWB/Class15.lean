import LeanUWB.Basic


-- ## Relations

class Relation (A : Type) where
  under : A → A → Prop

infix:51 " ⊑ " => Relation.under

class Poset (A : Type) extends Relation A where
  refle : ∀ x : A, x ⊑ x
  antis : ∀ x y : A, x ⊑ y ∧ y ⊑ x → x = y
  trans : ∀ x y z : A, x ⊑ y ∧ y ⊑ z → x ⊑ z


variable {A : Type}

-- Naming scheme (roughly) : `a ⊑ b ⊑ x ⊑ y ⊑ z`

-- ## Bounds

def Set.UpperBound [Poset A] (S : Set A) (z : A) : Prop :=
  ∀ x ∈ S, x ⊑ z

def Set.LowerBound [Poset A] (S : Set A) (a : A) : Prop :=
  ∀ x ∈ S, a ⊑ x

def Set.LeastUpperBound [Poset A] (S : Set A) (y : A) : Prop :=
  S.UpperBound y ∧ ∀ z : A, S.UpperBound z → y ⊑ z

def Set.GreatLowerBound [Poset A] (S : Set A) (b : A) : Prop :=
  S.LowerBound b ∧ ∀ a : A, S.LowerBound a → a ⊑ b

lemma Set.LeastUpperBound.is_unique [Poset A] {S : Set A} {x₁ x₂ : A}
    (hx₁ : S.LeastUpperBound x₁) (hx₂ : S.LeastUpperBound x₂) :
    x₁ = x₂ := by
  obtain ⟨x₁upper, x₁least⟩ := hx₁
  obtain ⟨x₂upper, x₂least⟩ := hx₂
  apply Poset.antis
  constructor
  · apply x₁least
    exact x₂upper
  · apply x₂least
    exact x₁upper

lemma Set.GreatLowerBound.is_unique [Poset A] {S : Set A} {x₁ x₂ : A}
    (hx₁ : S.GreatLowerBound x₁) (hx₂ : S.GreatLowerBound x₂) :
    x₁ = x₂ := by
  obtain ⟨x₁lower, x₁great⟩ := hx₁
  obtain ⟨x₂lower, x₂great⟩ := hx₂
  apply Poset.antis
  constructor
  · apply x₂great
    exact x₁lower
  · apply x₁great
    exact x₂lower

class CompleteLattic (A : Type) extends Poset A where
  hasSupre : ∀ S : Set A, ∃ y : A, S.LeastUpperBound y
  hasInfim : ∀ S : Set A, ∃ b : A, S.GreatLowerBound b


-- ## Extrema

noncomputable def supre [CompleteLattic A] (S : Set A) : A :=
  (CompleteLattic.hasSupre S).choose

noncomputable def infim [CompleteLattic A] (S : Set A) : A :=
  (CompleteLattic.hasInfim S).choose

prefix:999 "⊔" => supre
prefix:999 "⊓" => infim

lemma supre_is_upper [CompleteLattic A] (S : Set A) : S.UpperBound (⊔S) :=
  (CompleteLattic.hasSupre S).choose_spec.left

lemma infim_is_lower [CompleteLattic A] (S : Set A) : S.LowerBound (⊓S) :=
  (CompleteLattic.hasInfim S).choose_spec.left

lemma supre_is_least [CompleteLattic A] (S : Set A) (z : A) (hz : S.UpperBound z) : ⊔S ⊑ z :=
  (CompleteLattic.hasSupre S).choose_spec.right z hz

lemma infim_is_great [CompleteLattic A] (S : Set A) (a : A) (ha : S.LowerBound a) : a ⊑ ⊓S :=
  (CompleteLattic.hasInfim S).choose_spec.right a ha

lemma Set.LeastUpperBound.eq_supre [CompleteLattic A] {S : Set A} {x : A} (hx : S.LeastUpperBound x) :
    x = ⊔S := by
  apply Set.LeastUpperBound.is_unique
  · exact hx
  · constructor
    · apply supre_is_upper
    · apply supre_is_least

lemma Set.GreatLowerBound.eq_infim [CompleteLattic A] {S : Set A} {x : A} (hx : S.GreatLowerBound x) :
    x = ⊓S := by
  apply Set.GreatLowerBound.is_unique
  · exact hx
  · constructor
    · apply infim_is_lower
    · apply infim_is_great


-- ## Fixpoints

def Fixpoint (F : A → A) (x : A) : Prop :=
  F x = x

def Prefixpoint [Relation A] (F : A → A) (x : A) : Prop :=
  x ⊑ F x

def Posfixpoint [Relation A] (F : A → A) (x : A) : Prop :=
  F x ⊑ x

lemma prefixpoint_of_fixpoint [Poset A] {F : A → A} {x : A} (hx : Fixpoint F x) :
    Prefixpoint F x := by
  unfold Prefixpoint
  rw [hx]
  apply Poset.refle

lemma posfixpoint_of_fixpoint [Poset A] {F : A → A} {x : A} (hx : Fixpoint F x) :
    Posfixpoint F x := by
  unfold Posfixpoint
  rw [hx]
  apply Poset.refle

lemma fixpoint_of_pre_pos [Poset A] {F : A → A} {x : A} :
    Posfixpoint F x ∧ Prefixpoint F x → Fixpoint F x := by
  apply Poset.antis

def GreatFixpoint [Poset A] (F : A → A) (x : A) : Prop :=
  Fixpoint F x ∧ (Set.ofPred (Fixpoint F)).UpperBound x

def LeastFixpoint [Poset A] (F : A → A) (x : A) : Prop :=
  Fixpoint F x ∧ (Set.ofPred (Fixpoint F)).LowerBound x

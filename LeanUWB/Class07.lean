import LeanUWB.Class05


/--
Injective function is defined as a function without collisions.
-/
def Injectiv {A B : Type} (f : A → B) : Prop := ∀ x y : A, x ≠ y → f x ≠ f y

/--
Surjective function is defined as a function that returns all outputs.
-/
def Surjectiv {A B : Type} (f : A → B) : Prop := ∀ z : B, ∃ x : A, f x = z

/--
Bijective function is defined as a function that is injective and surjective at the same time.
-/
def Bijectiv {A B : Type} (f : A → B) : Prop := Injectiv f ∧ Surjectiv f

/--
Composition of injective functions is an injective function.
-/
theorem comp_injectiv {A B C : Type} {f : A → B} {g : B → C} (hf : Injectiv f) (hg : Injectiv g) :
    Injectiv (g ∘ f) := by
  intro x y hxy
  apply hg
  apply hf
  exact hxy

/--
If two functions are inverse to each other, the first function is bijective.
-/
theorem bijectiv_of_inverse {A B : Type} {f : A → B} {g : B → A}
    (hgf : ∀ a : A, g (f a) = a) (hfg : ∀ b : B, f (g b) = b) :
    Bijectiv f := by
  constructor
  · intro a₁ a₂ haa hfaa
    apply haa
    rw [←hgf a₁, ←hgf a₂, hfaa]
  · unfold Surjectiv
    by_contra! ⟨b, hb⟩
    have hfgb : f (g b) ≠ b
    · apply hb
    apply hfgb
    apply hfg

/--
If two functions are inverse to each other, both functions are bijective.
-/
theorem bijectiv_and_bijectiv_of_comp_eq_id_and_comp_eq_id {A B : Type} {f : A → B} {g : B → A}
    (hfg : f ∘ g = id) (hgf : g ∘ f = id) :
    Bijectiv f ∧ Bijectiv g := by
  have hgf' : ∀ a : A, g (f a) = a
  · intro a
    exact (congr_fun hgf a)
  have hfg' : ∀ b : B, f (g b) = b
  · intro b
    exact (congr_fun hfg b)
  constructor
  · exact bijectiv_of_inverse hgf' hfg'
  · exact bijectiv_of_inverse hfg' hgf'

/--
For no `T` there is a function that assigns sets from `T` to elements of `T` such that every set is an image of some element.
For finite `T` we could argue that `n < 2^n` where `n` is the cardinality, thus no surprise.
The interesting thing, however, is that the Cantor's theorem holds for infinite `T` as well.
-/
theorem thmCantor (T : Type) : ¬(∃ f : T → Set T, Surjectiv f) := by
  intro ⟨f, hf⟩
  obtain ⟨a, ha⟩ := hf { x : T | x ∉ f x }
  have hafa : (a ∈ f a) ↔ (a ∉ f a)
  · exact of_eq (congr_arg (a ∈ ·) ha)
  exact impossible_equivalence hafa

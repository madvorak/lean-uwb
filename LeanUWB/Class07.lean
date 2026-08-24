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

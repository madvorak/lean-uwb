import LeanUWB.Class08


/-- Motivation: -/
example : ∃ f : (ℕ → Fin 2) → (ℕ → Fin 3), Bijectiv f :=
  sorry -- See `Class09` for a solution.

/-- The ultimate goal of this exercise:  -/
example {A B : Type} (𝔸 : Set A) (𝔹 : Set B) :
    (∃ f : 𝔸 → 𝔹, Bijectiv f) ↔ ((∃ f : 𝔸 → 𝔹, Injectiv f) ∧ (∃ g : 𝔹 → 𝔸, Injectiv g)) :=
  sorry -- Do not prove here! See `Class09` for a finished proof.


-- First, we introduce some ad-hoc constructions...

/-- Inductive definition of the ancestor count when finite and acyclic:
    `Generation f g a n` means that the element `a : A` has exactly `n : ℕ` ancestors
    with respect to chaining `f : A → B` and `g : B → A` alternately
    (if `n` is not zero, then `g` was applied last). -/
private inductive Generation : {A B : Type} → (A → B) → (B → A) → A → ℕ → Prop
| zer {A B : Type} {f : A → B} {g : B → A} {a : A} (orphan : ¬ ∃ b : B, g b = a) :
    Generation f g a 0
| nex {A B : Type} {f : A → B} {g : B → A} {a : A} (p : B) (parent : g p = a) {n : ℕ} (their : Generation g f p n) :
    Generation f g a n.succ

/-- The ancestor count is unique. You probably won't need this lemma, but you may use it. -/
private lemma singleGeneration {A B : Type} {f : A → B} {g : B → A} {a : A} (hf : Injectiv f) (hg : Injectiv g) :
    ∀ m n : ℕ, Generation f g a m → Generation f g a n → m = n
| 0, 0, _, _ => rfl
| N+1, 0, fgaN, fga0 => by
  cases fgaN with
  | nex => cases fga0 with
  | zer => simp_all
| 0, M+1, fga0, fgaM => by
  cases fgaM with
  | nex => cases fga0 with
  | zer => simp_all
| N+1, M+1, fgaN, fgaM => by
  cases fgaN with
  | nex p parent pgen => cases fgaM with
  | nex q qarent qgen => rw [singleGeneration hg hf N M pgen (by
      convert qgen
      by_contra contr
      apply hg p q contr
      rw [parent, qarent]
    )]

variable {A B : Type} -- Do not move any higher!

/-- Definition of both `Aₑ` and `Bₑ` (depending on arguments). -/
private def EvenGeneration (f : A → B) (g : B → A) (a : A) : Prop :=
  ∃ n : ℕ, Generation f g a (2*n)

/-- Definition of both `Aₒ` and `Bₒ` (depending on arguments). -/
private def OddGeneration (f : A → B) (g : B → A) (a : A) : Prop :=
  ∃ n : ℕ, Generation f g a (2*n + 1)

/-- Every element of `Aₒ` has a parent. -/
private lemma OddGeneration.exists_parent {f : A → B} {g : B → A} {a : A}
    (oddGen : OddGeneration f g a) :
    ∃ p : B, g p = a ∧ EvenGeneration g f p := by
  sorry -- TODO

/-- If `a` is in `Aₒ`, then `f a` is in `Bₑ`. -/
private lemma OddGeneration.nextEvenGeneration {f : A → B} {g : B → A} {a : A}
    (oddGen : OddGeneration f g a) :
    EvenGeneration g f (f a) := by
  sorry -- TODO

/-- If `a` is in `Aₑ`, then `f a` is in `Bₒ`. -/
private lemma EvenGeneration.nextOddGeneration {f : A → B} {g : B → A} {a : A}
    (evenGen : EvenGeneration f g a) :
    OddGeneration g f (f a) := by
  sorry -- TODO

/-- If `f a` is in `Bₑ`, then `a` is in `Aₒ`. -/
private lemma EvenGeneration.prevOddGeneration {f : A → B} {g : B → A} {a : A}
    (evenGen : EvenGeneration g f (f a)) (hf : Injectiv f) :
    OddGeneration f g a := by
  sorry -- TODO

/-- This function is called `g⁻¹` in the textbook. For simplicity, we define it only as
    a function `Aₒ → B` (which is sufficient for proving the Schröder-Bernstein theorem). -/
private noncomputable def funOdd {f : A → B} {g : B → A} {a : A} (oddGen : OddGeneration f g a) : B :=
  oddGen.exists_parent.choose

/-- We have `g (g⁻¹ a) = a` for all `a` from `Aₒ`. -/
private lemma OddGeneration.g_funOdd {f : A → B} {g : B → A} {a : A} (oddGen : OddGeneration f g a) :
    g (funOdd oddGen) = a :=
  oddGen.exists_parent.choose_spec.left

/-- If `a` is from `Aₒ`, then we know that `g⁻¹ a` is from `Bₑ`. -/
private lemma OddGeneration.evenGen_funOdd {f : A → B} {g : B → A} {a : A} (oddGen : OddGeneration f g a) :
    EvenGeneration g f (funOdd oddGen) :=
  oddGen.exists_parent.choose_spec.right

/-- The function `g⁻¹` behaves on its domain like an injective function. -/
private lemma funOdd_ne_funOdd_of_ne {f : A → B} {g : B → A} {x y : A} (hxy : x ≠ y)
    (hxₒ : OddGeneration f g x) (hyₒ : OddGeneration f g y) :
    funOdd hxₒ ≠ funOdd hyₒ := by
  sorry -- TODO

/-- Finally, the Schröder-Bernstein theorem! -/
theorem thmSchroderBernstein :
    ((∃ f : A → B, Injectiv f) ∧ (∃ g : B → A, Injectiv g)) → (∃ f : A → B, Bijectiv f) := by
  intro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
  classical
  let F : A → B := fun a : A => if haₒ : OddGeneration f g a then funOdd haₒ else f a
  sorry -- TODO

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
  obtain ⟨n, hn⟩ := oddGen
  cases hn with
  | nex p parent their =>
    use p
    constructor
    · exact parent
    · use n

/-- If `a` is in `Aₒ`, then `f a` is in `Bₑ`. -/
private lemma OddGeneration.nextEvenGeneration {f : A → B} {g : B → A} {a : A}
    (oddGen : OddGeneration f g a) :
    EvenGeneration g f (f a) := by
  obtain ⟨k, hk⟩ := oddGen
  use k+1
  apply Generation.nex a -- or `right`
  · rfl
  exact hk

/-- If `a` is in `Aₑ`, then `f a` is in `Bₒ`. -/
private lemma EvenGeneration.nextOddGeneration {f : A → B} {g : B → A} {a : A}
    (evenGen : EvenGeneration f g a) :
    OddGeneration g f (f a) := by
  have ⟨k, hk⟩ := evenGen
  use k
  right
  · rfl
  exact hk

/-- If `f a` is in `Bₑ`, then `a` is in `Aₒ`. -/
private lemma EvenGeneration.prevOddGeneration {f : A → B} {g : B → A} {a : A}
    (evenGen : EvenGeneration g f (f a)) (hf : Injectiv f) :
    OddGeneration f g a := by
  have ⟨n, hn⟩ := evenGen
  cases n with
  | zero =>
    cases hn with
    | zer hfa =>
      exfalso
      apply hfa
      use a
  | succ k =>
    use k
    cases hn with
    | nex p hfpa hp =>
      have hpa : p = a
      · by_contra hpa
        exact hf p a hpa hfpa
      rw [hpa] at hp
      exact hp

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
  intro hhxhy
  apply hxy
  rw [←hxₒ.g_funOdd, ←hyₒ.g_funOdd]
  exact congr_arg g hhxhy

/-- Finally, the Schröder-Bernstein theorem! -/
theorem thmSchroderBernstein :
    ((∃ f : A → B, Injectiv f) ∧ (∃ g : B → A, Injectiv g)) → (∃ f : A → B, Bijectiv f) := by
  intro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
  classical
  let F : A → B := fun a : A => if haₒ : OddGeneration f g a then funOdd haₒ else f a
  use F
  constructor
  · intro x y hxy
    if hx : OddGeneration f g x then
      if hy : OddGeneration f g y then
        convert_to funOdd hx ≠ funOdd hy
        · exact dif_pos hx
        · exact dif_pos hy
        apply funOdd_ne_funOdd_of_ne
        exact hxy
      else
        convert_to funOdd hx ≠ f y
        · exact dif_pos hx
        · exact dif_neg hy
        intro hxfy
        have hhx := hx.evenGen_funOdd
        rw [hxfy] at hhx
        apply hy
        exact hhx.prevOddGeneration hf
    else
      if hy : OddGeneration f g y then
        convert_to f x ≠ funOdd hy
        · exact dif_neg hx
        · exact dif_pos hy
        intro hfxy
        have hhy := hy.evenGen_funOdd
        rw [←hfxy] at hhy
        apply hx
        exact hhy.prevOddGeneration hf
      else
        convert_to f x ≠ f y
        · exact dif_neg hx
        · exact dif_neg hy
        apply hf
        exact hxy
  · intro b
    sorry -- TODO

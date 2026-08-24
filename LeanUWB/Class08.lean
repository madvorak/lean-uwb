import LeanUWB.Class07

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

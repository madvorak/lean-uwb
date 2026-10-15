import LeanUWB.Exercises09


/-- We apply Schröder-Bernstein to solve the motivation example. -/
example : ∃ f : (ℕ → Fin 2) → (ℕ → Fin 3), Bijectiv f := by
  apply thmSchroderBernstein
  constructor
  · use (· · |>.castLE (show 2 ≤ 3 by norm_num))
    intro x₁ x₂ hxx
    rw [Function.ne_iff] at hxx ⊢
    obtain ⟨i, hi⟩ := hxx
    use i
    intro hxixi
    apply hi
    ext
    simpa using congr_arg Fin.val hxixi
  · use
      fun x : ℕ → Fin 3 => fun n : ℕ =>
        if n % 2 = 0 then
          if (x (n / 2)).val = 2 then 1 else 0
        else
          if (x (n / 2)).val = 1 then 1 else 0
    intro x₁ x₂ hxx
    rw [Function.ne_iff] at hxx ⊢
    obtain ⟨i, hi⟩ := hxx
    if x₁ i = 2 ∨ x₂ i = 2 then
      use 2 * i
      grind
    else
      use 2 * i + 1
      grind

/-- The reward for our hard work! -/
theorem exists_bijectiv_iff {A B : Type} (𝔸 : Set A) (𝔹 : Set B) :
    (∃ f : 𝔸 → 𝔹, Bijectiv f) ↔ ((∃ f : 𝔸 → 𝔹, Injectiv f) ∧ (∃ g : 𝔹 → 𝔸, Injectiv g)) := by
  constructor
  · intro ⟨f, inje, surje⟩
    constructor
    · exact ⟨f, inje⟩
    · use (Exists.choose <| surje ·)
      intro b₁ b₂ hbb haa
      apply hbb
      rw [←(surje b₁).choose_spec, ←(surje b₂).choose_spec]
      exact congr_arg f haa
  · apply thmSchroderBernstein

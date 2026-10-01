import LeanUWB.Class07
import LeanUWB.Solutions15

attribute [grind] Injectiv

theorem thmSchroderBernstein' {A B : Type} :
    ((∃ f : A → B, Injectiv f) ∧ (∃ g : B → A, Injectiv g)) → (∃ f : A → B, Bijectiv f) := by
  intro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
  obtain ⟨hfg, -⟩ := greatFixpoint_supre_prefixpoint (show Monoton (fun S : Set A => (g '' (f '' S)ᶜ)ᶜ) from
    ↓↓(compl_le_compl <| Set.image_mono <| compl_le_compl <| Set.image_mono ·))
  set P := ⊔ Prefixpoint (fun S : Set A => (g '' (f '' S)ᶜ)ᶜ)
  dsimp [Fixpoint] at hfg
  classical
  have hP : ∀ a ∉ P, ∃ b : B, g b = a
  · grind
  use fun a : A => if ha : a ∈ P then f a else (hP a ha).choose
  constructor
  · grind
  · intro b
    if hbfP : b ∈ f '' P then
      grind
    else
      use g b
      grind
-- Do you remember the proof from Exercises09.lean that was more than 150 lines long?

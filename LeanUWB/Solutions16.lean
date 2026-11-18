import LeanUWB.Class15

variable {A : Type} [CompleteLattic A]

noncomputable instance : Bot A where
  bot := ⊓ Set.univ

noncomputable instance : Top A where
  top := ⊔ Set.univ

lemma bot_under (x : A) : ⊥ ⊑ x := by
  apply infim_is_lower
  trivial

lemma top_above (x : A) : x ⊑ ⊤ := by
  apply supre_is_upper
  trivial

lemma above_iff_supre_pair (a b : A) :
    a ⊑ b ↔ ⊔ {a, b} = b := by
  constructor <;> intro hab
  · rw [←Set.LeastUpperBound.eq_supre]
    constructor
    · intro x hx
      cases hx with
      | inl ha =>
        rw [ha]
        exact hab
      | inr hb =>
        rw [hb]
        apply Poset.refle
    · intro x hx
      apply hx
      apply Set.mem_insert_of_mem
      rfl
  · rw [←hab]
    apply supre_is_upper
    apply Set.mem_insert

lemma under_iff_infim_pair (a b : A) :
    a ⊑ b ↔ ⊓ {a, b} = a := by
  constructor <;> intro hab
  · rw [←Set.GreatLowerBound.eq_infim]
    constructor
    · intro x hx
      cases hx with
      | inl ha =>
        rw [ha]
        apply Poset.refle
      | inr hb =>
        rw [hb]
        exact hab
    · intro x hx
      apply hx
      apply Set.mem_insert
  · rw [←hab]
    apply infim_is_lower
    apply Set.mem_insert_of_mem
    rfl

lemma JoinContinuous.monoton {F : A → A} (hF : JoinContinuous F) :
    Monoton F := by
  intro x y hxy
  have hFxy : F (⊔ {x, y}) = ⊔ {F x, F y} := by
    convert hF (fun i : ℕ => if i = 0 then x else y) (by
        intro
        have := Poset.refle y
        aesop
      ) using 1 <;>
    · congr
      apply Set.Subset.antisymm <;> intro z hz
      · cases hz with
        | inl hzx =>
          use 0
          exact hzx.symm
        | inr hzy =>
          use 1
          exact hzy.symm
      · obtain ⟨n, hn⟩ := hz
        cases n <;> simp_all
  rw [above_iff_supre_pair] at hxy ⊢
  rw [hxy] at hFxy
  exact hFxy.symm

lemma MeetContinuous.monoton {F : A → A} (hF : MeetContinuous F) :
    Monoton F := by
  intro x y hxy
  have hFxy : F (⊓ {x, y}) = ⊓ {F x, F y} := by
    convert hF (fun i : ℕ => if i = 0 then y else x) (by
        intro
        have := Poset.refle x
        aesop
      ) using 1 <;>
    · congr
      apply Set.Subset.antisymm <;> intro z hz
      · cases hz with
        | inl hzx =>
          use 1
          exact hzx.symm
        | inr hzy =>
          use 0
          exact hzy.symm
      · obtain ⟨n, hn⟩ := hz
        cases n <;> simp_all
  rw [under_iff_infim_pair] at hxy ⊢
  rw [hxy] at hFxy
  exact hFxy.symm

theorem JoinContinuous.constructLeastFixpoint {F : A → A} (hF : JoinContinuous F) :
    LeastFixpoint F (⊔ { F^[i] ⊥ | i : ℕ }) := by
  have important : ∀ n : ℕ, F^[n] ⊥ ⊑ F^[n.succ] ⊥
  · intro n
    induction n with
    | zero =>
      apply bot_under
    | succ _ ih =>
      convert hF.monoton _ _ ih using 1 <;> apply Function.iterate_succ_apply'
  constructor
  · set u := ⊔ { F^[i] ⊥ | i : ℕ }
    show F u = u
    rw [hF _ important]
    apply Poset.antis
    constructor
    · apply supre_is_least
      intro y ⟨i, hiy⟩
      apply supre_is_upper
      use i.succ
      rwa [Function.iterate_succ', Function.comp_apply]
    · apply supre_is_least
      intro y ⟨i, hiy⟩
      apply Poset.trans y (F y)
      constructor
      · rw [←hiy]
        convert important i using 1
        symm
        apply Function.iterate_succ_apply'
      · apply supre_is_upper
        use i
        rw [hiy]
  · intro y hy
    have under : ∀ i : ℕ, F^[i] ⊥ ⊑ y
    · intro i
      induction i with
      | zero =>
        apply bot_under
      | succ n ih =>
        rw [hy.symm, Function.iterate_succ_apply']
        apply hF.monoton
        exact ih
    apply supre_is_least _ y
    intro z ⟨i, hiz⟩
    specialize under i
    rwa [hiz] at under

theorem MeetContinuous.constructGreatFixpoint {F : A → A} (hF : MeetContinuous F) :
    GreatFixpoint F (⊓ { F^[i] ⊤ | i : ℕ }) := by
  have important : ∀ n : ℕ, F^[n.succ] ⊤ ⊑ F^[n] ⊤
  · intro n
    induction n with
    | zero =>
      apply top_above
    | succ _ ih =>
      convert hF.monoton _ _ ih using 1 <;> apply Function.iterate_succ_apply'
  constructor
  · set l := ⊓ { F^[i] ⊤ | i : ℕ }
    show F l = l
    rw [hF _ important]
    apply Poset.antis
    constructor
    · apply infim_is_great
      intro y ⟨i, hiy⟩
      apply Poset.trans _ (F y)
      constructor
      · apply infim_is_lower
        use i
        rw [hiy]
      · rw [←hiy]
        convert important i using 1
        symm
        apply Function.iterate_succ_apply'
    · apply infim_is_great
      intro y ⟨i, hiy⟩
      apply infim_is_lower
      use i.succ
      rwa [Function.iterate_succ', Function.comp_apply]
  · intro y hy
    have above : ∀ i : ℕ, y ⊑ F^[i] ⊤
    · intro i
      induction i with
      | zero =>
        apply top_above
      | succ n ih =>
        rw [hy.symm, Function.iterate_succ_apply']
        apply hF.monoton
        exact ih
    apply infim_is_great _ y
    intro z ⟨i, hiz⟩
    specialize above i
    rwa [hiz] at above

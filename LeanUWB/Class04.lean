import LeanUWB.Basic


example {P Q : Prop} (p : P) (pq : P → Q) : Q := by
  apply pq
  apply p

example {P Q : Prop} (p : P) (pq : P → Q) : Q := by
  apply pq
  exact p

example {P Q : Prop} (p : P) (pq : P → Q) : Q := by
  exact pq p

example {P Q : Prop} (p : P) (pq : P → Q) : Q :=
  pq p

-- for comparison: calling function
example {P Q : Type} (a : P) (f : P → Q) : Q :=
  f a


example {P Q R : Prop} (p : P) (pq : P → Q) (qr : Q → R) : R := by
  apply qr
  apply pq
  exact p

example {P Q R : Prop} (p : P) (pq : P → Q) (qr : Q → R) : R := by
  apply qr
  exact pq p

example {P Q R : Prop} (p : P) (pq : P → Q) (qr : Q → R) : R :=
  qr (pq p)

-- for comparison: calling functions
example {P Q R : Type} (a : P) (f : P → Q) (g : Q → R) : R :=
  g (f a)


example {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R := by
  intro p
  apply qr
  apply pq
  exact p

example {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R := by
  intro p
  exact qr (pq p)

example {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R := by
  exact fun p => qr (pq p)

example {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R :=
  fun p => qr (pq p)

example {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R :=
  qr ∘ pq

-- for comparison: composing functions
example {P Q R : Type} (f : P → Q) (g : Q → R) : P → R :=
  g ∘ f


example {P Q R S T : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (pqrst : P → Q → R → S → T) : T := by
  apply pqrst
  · exact p
  · apply pq
    exact p
  · apply qr
    apply pq
    exact p
  · apply rs
    apply qr
    apply pq
    exact p

example {P Q R S T : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (pqrst : P → Q → R → S → T) : T :=
  pqrst p (pq p) (qr (pq p)) (rs (qr (pq p)))

example {P Q R S T : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (pqrst : P → Q → R → S → T) : T := by
  have q : Q
  · exact pq p
  have r : R
  · exact qr q
  apply pqrst
  · exact p
  · exact q
  · exact r
  · exact rs r

example {P Q R S T : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (pqrst : P → Q → R → S → T) : T := by
  have q : Q
  · exact pq p
  have r : R
  · exact qr q
  have s : S
  · exact rs r
  exact pqrst p q r s

example {P Q R S T : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (pqrst : P → Q → R → S → T) : T := by
  tauto


example {P Q R S T U : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (rt : R → T) (stu : S → T → U) : U := by
  apply stu
  · apply rs
    apply qr
    apply pq
    exact p
  · apply rt
    apply qr
    apply pq
    exact p

example {P Q R S T U : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (rt : R → T) (stu : S → T → U) : U := by
  apply stu
  · apply rs
    exact qr (pq p)
  · apply rt
    exact qr (pq p)

example {P Q R S T U : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (rt : R → T) (stu : S → T → U) : U :=
  stu (rs (qr (pq p))) (rt (qr (pq p)))

example {P Q R S T U : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (rt : R → T) (stu : S → T → U) : U := by
  have r : R
  · apply qr
    exact pq p
  apply stu
  · apply rs
    exact r
  · apply rt
    exact r

example {P Q R S T U : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (rt : R → T) (stu : S → T → U) : U :=
  let r := qr (pq p)
  stu (rs r) (rt r)

example {P Q R S T U : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (rt : R → T) (stu : S → T → U) : U := by
  tauto

import LeanUWB.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt


structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

noncomputable def distance (A B : Point) : ℝ :=
  Real.sqrt ((A.x - B.x) ^ 2 + (A.y - B.y) ^ 2 + (A.z - B.z) ^ 2)

theorem distance_self (A : Point) : distance A A = 0 := by
  simp [distance]

theorem distance_comm (A B : Point) : distance A B = distance B A := by
  dsimp [distance]
  ring_nf

notation "𝕠" => Point.mk 0 0 0

theorem distance_origin (A : Point) : distance A 𝕠 = Real.sqrt (A.x ^ 2 + A.y ^ 2 + A.z ^ 2) := by
  simp [distance]


class BinOp (T : Type) where
  operate : T → T → T

infix:68 " ◆ " => BinOp.operate

class Semigrupa (T : Type) extends BinOp T where
  assoc : ∀ x y z : T, x ◆ (y ◆ z) = (x ◆ y) ◆ z

example (T : Type) [Semigrupa T] (a b c d : T) :
    (a ◆ b) ◆ (c ◆ d) = (a ◆ (b ◆ c)) ◆ d := by
  rw [Semigrupa.assoc, Semigrupa.assoc]


class Neutral (T : Type) where
  element : T

notation "𝟙" => Neutral.element

class Grupa (T : Type) extends Semigrupa T, Neutral T where
  operate_neutral : ∀ x : T, x ◆ 𝟙 = x
  neutral_operate : ∀ x : T, 𝟙 ◆ x = x
  operate_inverse : ∀ x : T, ∃ y : T, x ◆ y = 𝟙
  inverse_operate : ∀ x : T, ∃ y : T, y ◆ x = 𝟙

theorem right_inverse_unique {T : Type} [Grupa T] {x y₁ y₂ : T} (hxy₁ : x ◆ y₁ = 𝟙) (hxy₂ : x ◆ y₂ = 𝟙) :
    y₁ = y₂ := by
  obtain ⟨y, hy⟩ := Grupa.inverse_operate x
  have hyy₁ : y = y₁
  · calc y = y ◆ 𝟙   := by rw [Grupa.operate_neutral]
    _ = y ◆ (x ◆ y₁) := by rw [hxy₁]
    _ = (y ◆ x) ◆ y₁ := by rw [Semigrupa.assoc]
    _ = 𝟙 ◆ y₁       := by rw [hy]
    _ = y₁           := by rw [Grupa.neutral_operate]
  have hyy₂ : y = y₂
  · calc y = y ◆ 𝟙   := by rw [Grupa.operate_neutral]
    _ = y ◆ (x ◆ y₂) := by rw [hxy₂]
    _ = (y ◆ x) ◆ y₂ := by rw [Semigrupa.assoc]
    _ = 𝟙 ◆ y₂       := by rw [hy]
    _ = y₂           := by rw [Grupa.neutral_operate]
  rw [←hyy₁, ←hyy₂]

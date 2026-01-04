import Mathlib

/-
# Pset 2

## Problem 2.1

Prove the following lemmas:
-/

example : 2 + 2 = 4 := by
  sorry


abbrev SolutionSet (y : ℝ) : Set (ℝ × ℝ × ℝ × ℝ × ℝ) :=
 {(x₁, x₂, x₃, x₄, x₅) |
  (x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0 ∧ x₅ = 0) ∨
  (x₁ = x₂ ∧ x₂ = x₃ ∧ x₃ = x₄ ∧ x₄ = x₅ ∧ y = 2) ∨
  (y^2 + y - 1 = 0 ∧ ∃ s t,
    x₁ = s ∧
    x₂ = t ∧
    x₃ = y * t - s ∧
    x₄ = -(y * t) - y * s ∧
    x₅ = y * s - t)}

/-- Problem 4 from IMO 1963 -/
example : (x₁, x₂, x₃, x₄, x₅) ∈ SolutionSet y ↔
    (x₅ + x₂ = y * x₁ ∧
     x₁ + x₃ = y * x₂ ∧
     x₂ + x₄ = y * x₃ ∧
     x₃ + x₅ = y * x₄ ∧
     x₄ + x₁ = y * x₅) := by
  sorry


/-
## Problem 2.2

Prove the following lemmas:
-/

example : n ≤ 2 ^ n := by
  sorry


/-
## Problem 2.3

lsb
-/

/-
## Problem 2.4

PPM parser

-/

/-
## Problem 2.5

Quine

-/

/-
## Problem 2.6


-/

example [DecidableEq β] {A : Finset α} {g : α → Finset β}
    (hin : ∀ y, x ∈ g y → g (f y) ⊂ g y)
    (hnin : ∀ y, x ∉ g y → g (f y) = g y)
    (hf : ∀ y, x ∉ g (f y))
    (hA : ∃ a ∈ A, x ∈ g a)
    : (A.map f).biUnion g ⊂ A.biUnion g :=
  sorry

/-
## Problem 2.7

https://cjquines.com/files/binaryoperations.pdf
-/

example (f : α → α → α) l r (hl : ∀ x, f l x = x) (hr : ∀ x, f x r = x) : l = r := by
  sorry

example [Nonempty α] (f : α → α → α) (h : ∀ x y, ∃ z, f x z = y ∧ ∀ z', f x z = f x z' → z = z')
    : ∃ g : α → α → α, ∀ x y, f x (g x y) = y ∧ g x (f x y) = y := by
  sorry

example (f g : α → α → α) i j (hid : ∀ x, f i x = x ∧ f x i = x ∧ g j x = x ∧ g x j = x)
    (h : ∀ x y z w, f (g x y) (g z w) = g (f x z) (f y w)) : f = g := by
  sorry

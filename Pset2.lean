import Mathlib

/-
# Pset 2

## Problem 2.1

Prove the following lemmas:
-/

example : 2 + 2 = 4 := by
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

theorem mapped_list_is_ssubset [DecidableEq β] {list newlist : Finset α} {gather : α → Finset β}
    (h : newlist = list.map f)
    {uv : β}
    (hin : ∀ item, uv ∈ gather item → gather (f item) ⊂ gather item)
    (hnin : ∀ item, uv ∉ gather item → gather (f item) = gather item)
    (f_removes_uv : ∀ item, uv ∉ gather (f item))
    (hexists : ∃ a ∈ list, uv ∈ gather a)
    : newlist.biUnion gather ⊂ list.biUnion gather :=
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

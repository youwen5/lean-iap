import Mathlib

-- This is a comment

/-
This is also a comment

/-
Whoa, nested comments
-/
-/

-- Variables are immutable
def a := 1

#eval a

-- Get type of `a`
#check a





open symmDiff

instance : Add (Set α) := ⟨(· ∆ ·)⟩

@[simp]
lemma add_def {a b : Set α} : a + b = a ∆ b := rfl

instance : Zero (Set α) := ⟨{}⟩

@[simp]
lemma zero_def : (0 : Set α) = {} := rfl

instance : Neg (Set α) := ⟨id⟩

@[simp]
lemma neg_def {a : Set α} : -a = a := rfl

instance : Mul (Set α) := ⟨(· ∩ ·)⟩

@[simp]
lemma mul_def {a b : Set α} : a * b = a ∩ b := rfl

instance : One (Set α) := ⟨.univ⟩

@[simp]
lemma one_def : (1 : Set α) = .univ := rfl

example : CommRing (Set α) where
  add_assoc := by
    simp only [add_def]
    grind
  zero_add := by simp
  add_zero := by simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by simp
  add_comm := by
    simp only [add_def]
    grind
  left_distrib a b c := by
    ext x
    simp [symmDiff_def]
    grind
  right_distrib a b c := by
    ext x
    simp [symmDiff_def]
    grind
  zero_mul := by simp
  mul_zero := by simp
  mul_assoc := by
    simp only [mul_def]
    grind
  one_mul := by simp
  mul_one := by simp
  mul_comm := by
    simp only [mul_def]
    grind

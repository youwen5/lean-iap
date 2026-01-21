import Std
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

-- Output `a`
#eval a

-- Get type of `a`
#check a

def f (x : ℕ) := x ^ 2

#eval f 2


def gcd (a b : ℕ) :=
  if b > 0 then gcd b (a % b) else a
termination_by b
decreasing_by
  exact Nat.mod_lt a ‹_›

#loogle _ % _ < _


-- theorem is the same as def
theorem fst_of_two_props (a b : Prop) : a → b → a :=
  fun x _ ↦ x

#print fst_of_two_props

theorem fst_of_two_props' (a b : Prop) : a → b → a := by
  intro ha hb
  exact ha

#print fst_of_two_props'


theorem nng_theorem (h : x + y = 7) : 2 * (x + y) = 14 := by
  rw [h]

#print nng_theorem

theorem nng_theorem' (h : x + y = 7) : 2 * (x + y) = 14 := by
  grind

#print nng_theorem'._proof_1_1


structure Cluedump where
  title : String
  presenter : String
  room : String
  time : Std.Time.ZonedDateTime

def LeanCluedump1 : Cluedump := {
  title := "Lean Part 1"
  presenter := "xy"
  room := "3-370"
  time := zoned("2026-01-16T18:00:00-05:00")
}

#eval LeanCluedump1.room

def LeanCluedump2 := Cluedump.mk "Lean Part 2" "xy" "3-370" zoned("2026-01-20T18:00:00-05:00")

def LeanCluedump3 : Cluedump := ⟨"Lean Part 3", "xy", "3-370", zoned("2026-01-23T18:00:00-05:00")⟩

#check ℕ

#check Bool

#check True

#check False

#check And

#check Eq

example : Eq (2 + 2) 4 := by rfl

#check Option

-- Same thing as Option
inductive Maybe (α : Type)
  | none
  | some (val : α)

-- GADT syntax
inductive Maybe' (α : Type)
  | none
  | some : α → Maybe' α

def Maybe.check_if_none (x : Maybe α) :=
  match x with
  | none => "Nothing"
  | some _ => "Something"

def Maybe.check_if_none' : Maybe α → String
  | none => "Nothing"
  | some _ => "Something"


def my_add [Add α] (a b : α) := a + b

#eval 1.1 + 2.3

#synth Add Float


abbrev le (a b : (ℕ × String)) := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

instance : LE (ℕ × String) := ⟨le⟩

#synth LE (ℕ × String)

-- instance : LT (ℕ × String) := ⟨fun a b => a ≤ b ∧ ¬b ≤ a⟩

-- #synth LT (ℕ × String)

attribute [-instance] Prod.instPreorder Prod.instPartialOrder Prod.instMin_mathlib Prod.instMax_mathlib Prod.instLattice Prod.instDistribLattice Prod.instSemilatticeInf Prod.instSemilatticeSup

-- #synth SemilatticeInf (ℕ × String)

-- #synth Min (ℕ × String)

-- #synth Preorder (ℕ × String)

@[grind]
lemma le_def {a b : (ℕ × String)} : a ≤ b ↔ le a b := .rfl

instance : LinearOrder (ℕ × String) where
  le_refl := by grind
  le_trans := by grind
  le_antisymm := by grind
  le_total := by grind
  toDecidableLE a b := inferInstanceAs <| Decidable <| le a b


-- Symmetric difference and intersection form a commutative ring on a power set
open symmDiff

instance : Add (Set α) := ⟨(· ∆ ·)⟩

@[simp]
lemma add_def {a b : Set α} : a + b = a ∆ b := rfl

instance : Zero (Set α) := ⟨∅⟩

@[simp]
lemma zero_def : (0 : Set α) = ∅ := rfl

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


-- See Pset1.5.lean for today's problems

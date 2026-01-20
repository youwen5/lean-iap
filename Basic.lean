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


-- Warm fuzzy things
namespace Monad

#check List.map

#check Option.map

#check Except.map

class Functor' (f : Type → Type) where
  map : (α → β) → f α → f β

infixr:100 " <$> " => Functor'.map

class LawfulFunctor' f [Functor' f] where
  id_map (x : f α) : id <$> x = x
  comp_map (g : α → β) (h : β → γ) (x : f α) : (h ∘ g) <$> x = h <$> g <$> x


class Applicative' f extends Functor' f where
  pure' : α → f α
  seq : f (α → β) → f α → f β
export Applicative' (pure')

infixl:60 " <*> " => fun x y ↦ Applicative'.seq x y

class LawfulApplicative' f [Applicative' f] extends LawfulFunctor' f where
  pure_seq (g : α → β) (x : f α) : pure' g <*> x = g <$> x
  map_pure (g : α → β) (x : α) : g <$> (pure' x : f α) = pure' (g x)
  seq_pure (g : f (α → β)) (x : α) : g <*> pure' x = (· x) <$> g
  seq_assoc (x : f α) (g : f (α → β)) (h : f (β → γ)) : h <*> (g <*> x) = (· ∘ ·) <$> h <*> g <*> x
  comp_map g h x := (by
    repeat rw [← pure_seq]
    simp [seq_assoc, map_pure, seq_pure])


class Monad' m extends Applicative' m where
  bind : m α → (α → m β) → m β
  map f x := bind x (pure' ∘ f)
  seq f x := bind f (· <$> x)

infixl:55 " >>= " => Monad'.bind

class LawfulMonad' m [Monad' m] extends LawfulApplicative' m where
  bind_pure_comp (f : α → β) (x : m α) : x >>= (fun a ↦ pure' (f a)) = f <$> x
  bind_map (f : m (α → β)) (x : m α) : f >>= (· <$> x) = f <*> x
  pure_bind (x : α) (f : α → m β) : pure' x >>= f = f x
  bind_assoc (x : m α) (f : α → m β) (g : β → m γ) : x >>= f >>= g = x >>= fun y ↦ f y >>= g
  map_pure g x := (by rw [← bind_pure_comp, pure_bind])
  seq_pure g x := (by simp [← bind_map, map_pure, bind_pure_comp])
  seq_assoc x g h := (by simp [← bind_pure_comp, ← bind_map, bind_assoc, pure_bind])

@[simp]
instance : Monad' Option where
  pure' x := .some x
  bind x f := match x with
    | some x => f x
    | none => none

instance : LawfulMonad' Option where
  id_map := by
    simp
    grind
  pure_seq := by simp
  bind_pure_comp := by simp
  bind_map := by simp
  pure_bind := by simp
  bind_assoc := by
    simp
    grind


@[simp]
instance : Monad' List where
  pure' x := [x]
  bind xs f := xs.map f |>.flatten

instance : LawfulMonad' List where
  id_map xs := by
    simp
    induction xs <;> grind
  pure_seq := by simp
  bind_pure_comp f xs := by
    simp
    induction xs <;> grind
  bind_map := by simp
  pure_bind := by simp
  bind_assoc xs := by
    simp
    induction xs <;> grind

end Monad


-- https://slightknack.dev/blog/do-notation/

-- See Main.lean


def ICan'tBelieveItCanSort [LinearOrder α] (A : Array α) := Id.run do
  let N := A.size
  let mut A := A.toVector
  for hi : i in [:N] do
    for hj : j in [:N] do
      if A[i] < A[j] then
        A := A.swap i j
  return A.toArray


-- Local imperativity https://dl.acm.org/doi/10.1145/3547640
def kadane (A : Array ℤ) := Id.run do
  let mut cur := 0
  let mut ans := 0
  for x in A do
    cur := max x (cur + x)
    ans := max ans cur
  return ans


def UpToN (xs : List ℕ) : List ℕ := do
  let x ← xs
  let y ← List.range x
  return y

#eval UpToN [1, 2, 3]


-- Random exercises from MIL

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  sorry

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  sorry

example [Ring R] (a b : R) : a + b + -b = a := by
  sorry

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  sorry

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  sorry

example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : c < d) : a + Real.exp c + e < b + Real.exp d + e := by
  sorry

example (h : a ≤ b) : Real.log (1 + Real.exp a) ≤ Real.log (1 + Real.exp b) := by
  sorry

example : 0 ≤ a ^ 2 := by
  sorry

example (a b : ℝ) : |a*b| ≤ (a^2 + b^2)/2 := by
  sorry

example : min a b = min b a := by
  sorry

example : Nat.gcd m n = Nat.gcd n m := by
  sorry

example (h : a ≤ b) : 0 ≤ b - a := by
  sorry

example : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  sorry

example {n : ℕ} (h : Odd n) : Even n.succ := by
  sorry

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  sorry

def SumOfSquares [CommRing α] (x : α) := ∃ a b, x = a ^ 2 + b ^ 2

example [CommRing α] {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) : SumOfSquares (x * y) := by
  sorry

open Function in
example {g : β → γ} {f : α → β} (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  sorry

example (P : α → Prop) (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  sorry

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  sorry

example {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by
  sorry

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  sorry

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  sorry

example : ∀ f : α → Set α, ¬Function.Surjective f := by
  sorry

example (n : ℕ) : ∑ i ∈ Finset.range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  sorry

example : ∀ n, ∃ p > n, Nat.Prime p := by
  sorry

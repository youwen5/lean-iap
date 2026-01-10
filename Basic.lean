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


def my_add [Add α] (a b : α) := a + b

#eval 1.1 + 2.3

#synth Add Float


def BadSort [LinearOrder α] (A : List α)
  | 0 => A.insertionSort (· ≤ ·)
  | Nat.succ n => BadSort A.permutations n |>.headD []

def WorstSort [LinearOrder α] (A : List α) (f : ℕ → ℕ) :=
  BadSort A <| f A.length

def DiabolicalSort [LinearOrder α] (A : List α) :=
  WorstSort A (fun n ↦ ack n n)


-- Warm fuzzy things
namespace Monad

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


namespace Sorting

variable [LE α] [DecidableLE α] [Std.IsLinearOrder α] [BEq α] [LawfulBEq α] (xs : List α)

@[grind]
def insert (a : α)
  | [] => [a]
  | x :: xs =>
    if a ≤ x then
      a :: x :: xs
    else
      x :: insert a xs

@[grind]
def insertionSort : List α → List α
  | [] => []
  | x :: xs => insert x (insertionSort xs)

@[grind]
def Sorted : List α → Prop
  | [] | [_] => True
  | x :: x' :: xs => x ≤ x' ∧ Sorted (x' :: xs)
/-
This also works:
inductive Sorted : List α → Prop where
  | nil : Sorted []
  | single x : Sorted [x]
  | cons_cons x x' xs : x ≤ x' → Sorted (x' :: xs) → Sorted (x :: x' :: xs)
-/

theorem insertCorrect x : (Sorted xs → Sorted (insert x xs)) ∧ (x :: xs).Perm (insert x xs) := by
  induction xs with
  | nil => grind
  | cons _ t => cases t <;> grind

theorem insertionSortCorrect : Sorted (insertionSort xs) ∧ xs.Perm (insertionSort xs) := by
  induction xs with
  | nil => grind
  | cons h t => grind [insertCorrect (insertionSort t) h]


def ICan'tBelieveItCanSort [LinearOrder α] (A : Array α) := Id.run do
  let N := A.size
  let mut A := A.toVector
  for hi : i in [:N] do
    for hj : j in [:N] do
      if A[i] < A[j] then
        A := A.swap i j
  return A.toArray

end Sorting


-- This example is from the Lean homepage

/-- A prime is a number larger than 1 with no trivial divisors -/
def IsPrime (n : Nat) := 1 < n ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n

/-- Every number larger than 1 has a prime factor -/
theorem exists_prime_factor :
    ∀ n, 1 < n → ∃ k, IsPrime k ∧ k ∣ n := by
  intro n h1
  -- Either `n` is prime...
  by_cases hprime : IsPrime n
  · grind [Nat.dvd_refl]
  -- ... or it has a non-trivial divisor with a prime factor
  · obtain ⟨k, _⟩ : ∃ k, 1 < k ∧ k < n ∧ k ∣ n := by
      simp_all [IsPrime]
    obtain ⟨p, _, _⟩ := exists_prime_factor k (by grind)
    grind [Nat.dvd_trans]

/-- The factorial, defined recursively, with custom notation -/
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n + 1) * factorial n
notation:10000 n "!" => factorial n

/-- The factorial is always positive -/
theorem factorial_pos : ∀ n, 0 < n ! := by
  intro n; induction n <;> grind [factorial]

/-- ... and divided by its constituent factors -/
theorem dvd_factorial : ∀ n, ∀ k ≤ n, 0 < k → k ∣ n ! := by
  intro n; induction n <;>
    grind [Nat.dvd_mul_right, Nat.dvd_mul_left_of_dvd, factorial]

/--
We show that we find arbitrary large (and thus infinitely
many) prime numbers, by picking an arbitrary number `n`
and showing that `n! + 1` has a prime factor larger than `n`.
-/
theorem InfinitudeOfPrimes : ∀ n, ∃ p > n, IsPrime p := by
  intro n
  have : 1 < n ! + 1 := by grind [factorial_pos]
  obtain ⟨p, hp, _⟩ := exists_prime_factor (n ! + 1) this
  suffices ¬p ≤ n by grind
  intro (_ : p ≤ n)
  have : 1 < p := hp.1
  have : p ∣ n ! := dvd_factorial n p ‹p ≤ n› (by grind)
  have := Nat.dvd_sub ‹p ∣ n ! + 1› ‹p ∣ n !›
  grind [Nat.add_sub_cancel_left, Nat.dvd_one]

#print InfinitudeOfPrimes

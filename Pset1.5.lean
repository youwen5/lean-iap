import Mathlib

-- Random exercises from MIL

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  sorry

example (a b c d : ℝ) : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  sorry

example (a b : ℤ) : a + b + -b = a := by
  sorry

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  sorry

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  sorry

example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : c < d) : a + Real.exp c + e < b + Real.exp d + e := by
  sorry

example (a b : ℝ) (h : a ≤ b) : Real.log (1 + Real.exp a) ≤ Real.log (1 + Real.exp b) := by
  sorry

example : 0 ≤ a ^ 2 := by
  sorry

example (a b : ℝ) : |a*b| ≤ (a^2 + b^2)/2 := by
  sorry

example (a b : ℝ) : min a b = min b a := by
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

-- Exercises from TPIL and other random sources

namespace TPIL

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  sorry

end TPIL

namespace InsertionSort

variable [LinearOrder α] (xs : List α)

def ins (a : α)
  | [] => [a]
  | x :: xs =>
    if a ≤ x then a :: x :: xs else x :: ins a xs

def insSort : List α → List α
  | [] => []
  | x :: xs => ins x (insSort xs)

inductive Sorted : List α → Prop where
  | nil : Sorted []
  | single x : Sorted [x]
  | cons_cons x x' xs : x ≤ x' → Sorted (x' :: xs) → Sorted (x :: x' :: xs)

theorem insertCorrect x : (Sorted xs → Sorted (ins x xs)) ∧ (x :: xs).Perm (ins x xs) := by
  sorry

theorem insertionSortCorrect : Sorted (insSort xs) ∧ xs.Perm (insSort xs) := by
  sorry

end InsertionSort

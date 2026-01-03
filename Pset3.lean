import Std.Tactic.Do
import Mathlib

open Std.Do

/-
# Pset 3

## Problem 3.1

In Python, we can use `'We are the {} who say "{}!"'.format('knights', 'Ni')` (or f-strings in modern Python) to fill in values in a string with placeholders. Similarly, in Rust we can use `println!("{:?} {}", [1, 2, 3], "hi")` to print out a string with the placeholders filled in with the function arguments. But what are the types of `format()` and `println!()`? These functions take in a variable number of arguments, depending on the number of placeholders in the string, and for `println!()`, `{:?}` corresponds to arrays and `{}` corresponds to regular values.

Python sidesteps the question by being dynamically typed, ew. Rust also cheats here using a macro, which is also the approach used by Lean's f-string equivalent, `s!""`. These languages don't have type systems that are strong enough to express the type of a string format function, but Lean does! In this problem, we will write a `format` function




-/


inductive Fmt where
  | Arg : Fmt → Fmt
  | Nat : Fmt → Fmt
  | Char : Char → Fmt → Fmt
  | End




/-
## Problem 3.2

Here's a weird sorting algorithm:
-/

namespace Sorting

variable [LinearOrder α] (A : Array α)

def ICan'tBelieveItCanSort := Id.run do
  let N := A.size
  let mut A := A.toVector
  for hi : i in [:N] do
    for hj : j in [:N] do
      if A[i] < A[j] then
        A := A.swap i j
  return A.toArray

#eval ICan'tBelieveItCanSort #[69, 420, 1, 1, 13, 1, 65536]

/-
First, write a natural language proof for why this algorithm is correct.

Next, prove in Lean that the algorithm returns a permutation of its input.
-/

theorem perm : ICan'tBelieveItCanSort A |>.Perm A := by
  generalize h : ICan'tBelieveItCanSort A = x
  apply Id.of_wp_run_eq h
  mvcgen
  sorry

/-
Now for the fun part!
-/

theorem sorted : ICan'tBelieveItCanSort A |>.Pairwise (· ≤ ·) := by
  generalize h : ICan'tBelieveItCanSort A = x
  apply Id.of_wp_run_eq h
  mvcgen
  sorry

/-
Now we can declare victory!
-/

theorem ICan'tBelieveICanProveItCanSort : (ICan'tBelieveItCanSort A).Perm A
    ∧ (ICan'tBelieveItCanSort A).Pairwise (· ≤ ·) :=
  ⟨perm A, sorted A⟩

end Sorting

/-
## Problem 3.3
-/

namespace Kadane

def kadane (A : Array ℤ) := Id.run do
  let mut cur := 0
  let mut ans := 0
  for x in A do
    cur := max x (cur + x)
    ans := max ans cur
  return ans

def is_max_nonempty_suffix (xs : List ℤ) m :=
  (∃ i ≤ xs.length, (xs.drop i).sum = m) ∧ ∀ i < xs.length, (xs.drop i).sum ≤ m

def is_max_subarray (xs : List ℤ) m :=
  0 ≤ m ∧ (∃ i ≤ xs.length, ∃ j ≤ xs.length, (xs.extract i j).sum = m) ∧ ∀ i ≤ xs.length, ∀ j ≤ xs.length, (xs.extract i j).sum ≤ m

lemma drop_append_sum [AddMonoid α] {xs ys : List α} (hi : i ≤ xs.length) : (xs ++ ys |>.drop i).sum = (xs.drop i).sum + ys.sum := by
  sorry

lemma extract_end_drop {xs : List α} (h : j = xs.length) : xs.extract i j = xs.drop i := by
  sorry

lemma extract_in_bounds {xs ys : List α} (hi : i ≤ xs.length) (hj : j ≤ xs.length) : (xs ++ ys).extract i j = xs.extract i j := by
  sorry

theorem kadane_correct : is_max_subarray A.toList (kadane A) := by
  generalize h : kadane A = x
  apply Id.of_wp_run_eq h
  mvcgen
  sorry

end Kadane

/-
## Problem 3.4

fenwick
-/

namespace Fenwick

end Fenwick

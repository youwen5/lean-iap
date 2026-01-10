import Std.Tactic.Do
import Mathlib

open Std.Do

/-
# Pset 3

## Problem 3.1


-/

lemma imo1964_p1b (n : ℕ) : (2 ^ n + 1) % 7 ≠ 0 := by
  sorry

abbrev solution_set : Set (ℂ × ℂ × ℂ) := { ⟨1, 1, 1⟩ }

lemma usa1973_p4 (x y z : ℂ) :
    x + y + z = 3 ∧
    x ^ 2 + y ^ 2 + z ^ 2 = 3 ∧
    x ^ 3 + y ^ 3 + z ^ 3 = 3 ↔ ⟨x,y,z⟩ ∈ solution_set := by
  sorry

-- structure MultisetNatOfLen14 where
--   s : Multiset ℕ
--   p : Multiset.card s = 14

abbrev SolutionSet : Set <| Vector ℕ 14 := sorry

lemma usa1979_p1 : ∀ e, e ∈ SolutionSet ↔ (e.map (· ^ 4)).sum = 1599 := by
  sorry


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

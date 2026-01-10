import Std.Tactic.Do
import Mathlib

open Std.Do

/-
# Pset 3

## Problem 3.1

Prove the following lemma.
-/

lemma bounded_by_reciprocals (x : ℝ) (hx : 0 ≤ x) (h : ∀ n, x ≤ 1 / n) : x = 0 := by
  sorry

/-
## Problem 3.2

Prove the following lemmas.
-/

lemma imo1964_p1b (n : ℕ) : (2 ^ n + 1) % 7 ≠ 0 := by
  sorry

abbrev SolutionSet : Set <| Vector ℕ 14 := sorry

lemma usa1979_p1 : ∀ e, e ∈ SolutionSet ↔ (e.map (· ^ 4)).sum = 1599 := by
  sorry

/-
## Problem 3.3

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
## Problem 3.4

-/

/-
## Problem 3.5

-/

/-
## Problem 3.6

-/

/-
## Problem 3.7

-/

/-
## Problem 3.8

-/

/-
## Problem 3.9

-/

def solution : String := sorry

open Nat Real Quaternion CoxeterMatrix Lean in
example : minFac '⓫'.toNat|>λ_11↦(·+97)<$>[0/0,_11,-(⟨1,0,2,4⟩:ℍ[ℤ])^2|>.re.toNat,defaultMaxRecDepth%101,catalan 4,_11,(φ∘φ∘φ∘φ∘φ∘φ<|4‼‼)!,↑((4:Fin 24)-6),⌈deriv (sin ·^69) π⌉₊,_11,Nat.card<|Aₙ 2|>.Group]
    = solution.toList.map Char.toNat := by
  sorry



/-
## Problem 3.10

fenwick
-/

namespace Fenwick

end Fenwick

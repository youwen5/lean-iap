import Std.Tactic.Do
import Mathlib

-- https://leanprover.zulipchat.com/#narrow/channel/236446-Type-theory/topic/Paradoxes.20and.20Type.20Universes/with/538016579

axiom Bad : Type

axiom bad : (α : Type) × α ↪ Bad

noncomputable section

def k (P : Bad → Prop) : Bad :=
  bad ⟨Bad → Prop, P⟩

def Q (b : Bad) : Prop :=
  ∃ P, k P = b ∧ ¬P b

theorem k_injective : k.Injective :=
  fun _ _ hab => eq_of_heq
    (Sigma.mk.inj (bad.injective hab)).2

theorem down (h : Q (k Q)) : ¬Q (k Q) :=
  h.elim fun _ hP =>
    (congrArg Not (congrFun (k_injective hP.1) (k Q))).mp hP.2

theorem up (h : ¬Q (k Q)) : Q (k Q) :=
  ⟨Q, rfl, h⟩

theorem false : False :=
  down (up fun h => down h h) (up fun h => down h h)

-- 'false' depends on axioms: [Bad, bad]
#print axioms _root_.false









-- TODO: prove binary search

def Array.binarySearch (A : Array ℕ) (x : ℕ) := Id.run do
  let n := A.size
  let mut l : Fin (n + 1) := 0
  let mut r : Fin (n + 1) := ⟨n, by grind⟩
  while h : l < r do
    let m : Fin (n + 1) := ⟨(l.val + r.val) / 2, by grind⟩
    if A[m]'(by grind) < x then
      l := m + 1
    else
      r := m
  return l

open Std.Do in
lemma binarySearchCorrect (A : Array ℕ) (hA : A.Pairwise (· ≤ ·)) : ∀ i (hi : i < A.binarySearch x), A[i] < x := by
  sorry

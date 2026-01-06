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

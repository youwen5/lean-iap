import Mathlib


-- Review type classes (very different from classes in OOP!)

-- Warm fuzzy things
namespace Monad

#eval [1, 2, 3].map (· * 2)

#eval (some 2).map (· * 2)

#eval none.map (· * 2)

#eval (· * 2) <$> [1, 2, 3]

#check List.map

#check Option.map

#check Except.map

#check Tree.map

class Functor' (f : Type → Type) where
  map : (α → β) → f α → f β

scoped infixr:100 " <$> " => Functor'.map

scoped infixr:100 " 🤑 " => Functor.map

#eval (· * 2) 🤑 [1, 2, 3]

class LawfulFunctor' f [Functor' f] where
  id_map (x : f α) : id <$> x = x
  comp_map (g : α → β) (h : β → γ) (x : f α) : (h ∘ g) <$> x = h <$> g <$> x

@[simp]
instance : Functor' Option where
  map f
    | some x => some (f x)
    | none => none

instance : LawfulFunctor' Option where
  id_map x := by cases x <;> simp
  comp_map g h x := by cases x <;> simp

@[simp]
instance (α : Type) : Functor' (α → ·) where
  map f g := f ∘ g

instance (α : Type) : LawfulFunctor' (α → ·) where
  id_map := by simp
  comp_map := by simp [Function.comp_assoc]


#simp (some 3).map (· * ·)

class Applicative' f extends Functor' f where
  pure : α → f α
  seq : f (α → β) → f α → f β
export Applicative' (pure)

scoped infixl:60 " <*> " => Applicative'.seq

class LawfulApplicative' f [Applicative' f] extends LawfulFunctor' f where
  pure_seq (g : α → β) (x : f α) : pure g <*> x = g <$> x
  map_pure (g : α → β) (x : α) : g <$> (pure x : f α) = pure (g x)
  seq_pure (g : f (α → β)) (x : α) : g <*> pure x = (· x) <$> g
  seq_assoc (x : f α) (g : f (α → β)) (h : f (β → γ)) : h <*> (g <*> x) = (· ∘ ·) <$> h <*> g <*> x
  comp_map g h x := (by
    repeat rw [← pure_seq]
    simp [seq_assoc, map_pure, seq_pure])

#eval ((· * ·) <$> (Except.ok 3) <*> (Except.ok 4) : Except String ℕ)

@[simp]
instance (α : Type) : Applicative' (α → ·) where
  pure x := fun _ ↦ x
  seq f g := fun x ↦ f x (g x)

instance (α : Type) : LawfulApplicative' (α → ·) where
  pure_seq := by simp; grind
  map_pure := by simp; grind
  seq_pure := by simp; grind
  seq_assoc := by simp


def one_over (x : ℕ) : Option ℚ :=
  if x = 0 then
    none -- Division by 0 is undefined
  else
    some <| 1 / x

#eval one_over 2

#eval one_over (some 2)

#eval (some 2) >>= one_over


class Monad' m extends Applicative' m where
  bind : m α → (α → m β) → m β
  map f x := bind x (pure ∘ f)
  seq f x := bind f (· <$> x)

scoped infixl:55 " >>= " => Monad'.bind

class LawfulMonad' m [Monad' m] extends LawfulApplicative' m where
  bind_pure_comp (f : α → β) (x : m α) : x >>= (fun a ↦ pure (f a)) = f <$> x
  bind_map (f : m (α → β)) (x : m α) : f >>= (· <$> x) = f <*> x
  pure_bind (x : α) (f : α → m β) : pure x >>= f = f x
  bind_assoc (x : m α) (f : α → m β) (g : β → m γ) : x >>= f >>= g = x >>= fun y ↦ f y >>= g
  map_pure g x := (by rw [← bind_pure_comp, pure_bind])
  seq_pure g x := (by simp [← bind_map, map_pure, bind_pure_comp])
  seq_assoc x g h := (by simp [← bind_pure_comp, ← bind_map, bind_assoc, pure_bind])

@[simp]
instance (α : Type) : Monad' (α → ·) where
  bind f g := fun x ↦ g (f x) x

instance (α : Type) : LawfulMonad' (α → ·) where
  bind_pure_comp := by simp; grind
  bind_map := by simp
  pure_bind := by simp
  bind_assoc := by simp

@[simp]
instance : Monad' Option where
  pure x := .some x
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
  pure x := [x]
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


def option_div (x_wrapped : Option ℕ) (y_wrapped : Option ℕ) : Option ℚ :=
  y_wrapped >>= fun y ↦
    if y = 0 then
      none
    else
      x_wrapped >>= fun x ↦ some <| x / y

#eval option_div (some 3) (some 0)

def option_div' (x_wrapped : Option ℕ) (y_wrapped : Option ℕ) : Option ℚ := do
  let x ← x_wrapped
  let y ← y_wrapped
  if y = 0 then none else some <| x / y


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


def Array.insSort [LinearOrder α] (A : Array α) := Id.run do
  let N := A.size
  let mut A := A.toVector
  for hi : i in [:N] do
    for hj : j in [:i] do
      have := Membership.get_elem_helper hi rfl
      if A[i - j] < A[i - j - 1] then
        A := A.swap (i - j - 1) (i - j)
      else
        break
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


namespace Imperative

open Std.Do

variable [LinearOrder α] (A : Array α)

theorem insSortPerm : A.insSort.Perm A := by
  generalize h : A.insSort = x
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨_, A'⟩ => ⌜A.Perm A'.toArray⌝
  · ⇓⟨_, A'⟩ => ⌜A.Perm A'.toArray⌝
  with grind [Array.Perm.trans, Array.Perm.symm, Array.swap_perm]

abbrev Sorted := ∀ i (_ : 0 ≤ i ∧ i < A.size - 1), A[i] ≤ A[i + 1]

abbrev SortedRange l r (_ : l ≤ A.size := by grind) (_ : r ≤ A.size := by grind) :=
  ∀ i (_ : l ≤ i ∧ i < r - 1), A[i] ≤ A[i + 1]

theorem insSortSorted : Sorted A.insSort := by
  generalize h : A.insSort = x
  apply Id.of_wp_run_eq h
  mvcgen <;> expose_names
  · exact ⇓⟨xs, A'⟩ => ⌜SortedRange A'.toArray 0 xs.pos (by grind) (by grind [List.length_append, xs.property])⌝
  · exact ⇓⟨xs, A'⟩ => ⌜SortedRange A'.toArray 0 (cur - xs.pos) ∧ SortedRange A'.toArray (cur - xs.pos) (cur + 1)
      ∧ ((_ : 0 < xs.pos ∧ xs.pos < cur) → A'[cur - xs.pos - 1]'(by grind) ≤ A'[cur - xs.pos + 1]'(by grind))⌝
  case vc1.step.isTrue =>
    simp at h_5 ⊢
    and_intros
    · grind
    · intro i hi
      by_cases i = cur - cur_1 - 1 ∨ i = cur - cur_1
      · grind
      · grind [h_5.2.1 i (by grind)]
    · intro _
      grind [h_5.1 (cur - cur_1 - 2) (by grind)]
  case vc2.step.isFalse =>
    simp_all
    and_intros
    · grind
    · intro i hi
      by_cases i < cur - cur_1 - 1
      · exact h_5.1 i (by grind)
      · by_cases cur - cur_1 ≤ i
        · exact h_5.2.1 i (by grind)
        · grind
    · grind
  case vc4.step.post.success =>
    simp at h_3 ⊢
    grind
  all_goals grind

theorem insSortCorrect : A.insSort.Perm A ∧ Sorted A.insSort :=
  ⟨insSortPerm A, insSortSorted A⟩

end Imperative

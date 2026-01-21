import Mathlib


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

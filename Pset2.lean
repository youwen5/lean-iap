import Mathlib

/-
# Pset 2

## 2.1

Prove the following lemmas in Lean.
-/

lemma two_plus_two : 2 + 2 = 4 := by
  sorry

lemma and_swap : p ∧ q → q ∧ p := by
  sorry

lemma add_rearrange {a b c d : ℝ} : 0 ≤ a + b + c + d ↔ -b - c ≤ a + d := by
  sorry

lemma three_not_even {x : ℤ} : 2 * x ≠ 3 := by
  sorry

lemma linear_arithmetic {a b c d e f : ℝ} :
    2 * a + b ≥ 1 →
    b ≥ 0 → c ≥ 0 → d ≥ 0 → e * f ≥ 0 →
    a ≥ 3 * c →
    c ≥ 6 * e * f → d - f * e * 5 ≥ 0 →
    a + b + 3 * c + d + 2 * e * f < 0 →
    False := by
  sorry

lemma cross_multiply_field [Field α] {x y z w : α} :
    x / y = z / w →
    y ≠ 0 → w ≠ 0 →
    x * w = z * y := by
  sorry

abbrev SolutionSet (y : ℝ) : Set (ℝ × ℝ × ℝ × ℝ × ℝ) :=
 {(x₁, x₂, x₃, x₄, x₅) |
  (x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0 ∧ x₅ = 0) ∨
  (x₁ = x₂ ∧ x₂ = x₃ ∧ x₃ = x₄ ∧ x₄ = x₅ ∧ y = 2) ∨
  (y^2 + y - 1 = 0 ∧ ∃ s t,
    x₁ = s ∧
    x₂ = t ∧
    x₃ = y * t - s ∧
    x₄ = -(y * t) - y * s ∧
    x₅ = y * s - t)}

lemma imo1963_p4 : (x₁, x₂, x₃, x₄, x₅) ∈ SolutionSet y ↔
    (x₅ + x₂ = y * x₁ ∧
     x₁ + x₃ = y * x₂ ∧
     x₂ + x₄ = y * x₃ ∧
     x₃ + x₅ = y * x₄ ∧
     x₄ + x₁ = y * x₅) := by
  sorry

/-
## 2.2

Prove the following lemmas.
-/

lemma pow_two_larger : n ≤ 2 ^ n := by
  sorry

lemma pow_two_larger' (h : 2 ≤ n) : (n - 2) * 2 ≤ 2 ^ (n - 1) := by
  sorry

/-
## 2.3

Prove these lemmas about binary operations (taken from https://cjquines.com/files/binaryoperations.pdf).
-/

lemma cjq1 (f : α → α → α) (hl : ∀ x, f l x = x) (hr : ∀ x, f x r = x) : l = r := by
  sorry

lemma cjq2 [Nonempty α] (f : α → α → α) (h : ∀ x y, ∃ z, f x z = y ∧ ∀ z', f x z = f x z' → z = z')
    : ∃ g : α → α → α, ∀ x y, f x (g x y) = y ∧ g x (f x y) = y := by
  sorry

lemma cjq3 (f g : α → α → α) (hid : ∀ x, f i x = x ∧ f x i = x ∧ g j x = x ∧ g x j = x)
    (h : ∀ x y z w, f (g x y) (g z w) = g (f x z) (f y w)) : f = g := by
  sorry

/-
## 2.4

Write a recursive function that computes the index of least significant bit of a natural number `x`, i.e. the largest `k` such that `2 ^ k` divides `x`. Prove your that your function terminates and is correct.
-/

def lsb (x : ℕ) (hx : 0 < x) : ℕ :=
  sorry

lemma lsb_div (x : ℕ) (hx : 0 < x) : 2 ^ lsb x hx ∣ x := by
  sorry

lemma lsb_largest (x : ℕ) (hx : 0 < x) : ∀ k > lsb x hx, ¬2 ^ k ∣ x := by
  sorry

/-
## 2.5

Create a `structure` called `Color` to represent RGB colors. Then write a function that parses a [P6 PPM image](https://en.wikipedia.org/wiki/Netpbm#PPM_example) and returns an `Except` type with either an `Array (Array Color)` or an error message string. Prove that all array accesses are in bounds.
-/

def parsePPM (bytes : ByteArray) := do
  sorry

/-
## 2.6

Create a new file called `Quine.lean` and add it as a `[[lean_exe]]` in the `lakefile.toml` file. Then write a [quine](https://en.wikipedia.org/wiki/Quine_(computing)) in Lean and run it with `lake exe`.

## 2.7

Prove the following lemma.
-/

lemma crazy_lemma [DecidableEq β] {A : Finset α} {g : α → Finset β}
    (hin : ∀ y, x ∈ g y → g (f y) ⊂ g y)
    (hnin : ∀ y, x ∉ g y → g (f y) = g y)
    (hf : ∀ y, x ∉ g (f y))
    (hA : ∃ a ∈ A, x ∈ g a)
    : (A.map f).biUnion g ⊂ A.biUnion g :=
  sorry

/-
## 2.8

Implement applicative `seq` for a monad, first without using `do` notation, and then simplify your implementation using `do`.

Furthermore, given the `fish` operator, implement the other two equivalent formulations of monads.
-/

def appSeq [Monad m] (fs : m (α → β)) (as : m α) : m β :=
  sorry

def appSeqDo [Monad m] (fs : m (α → β)) (as : m α) : m β := do
  sorry

def joinFromFish (m : Type u → Type u) (fish : {α β γ : Type u} → (α → m β) → (β → m γ) → α → m γ) :
    m (m α) → m α :=
  sorry

def bindFromFish (m : Type u → Type u) (fish : {α β γ : Type u} → (α → m β) → (β → m γ) → α → m γ) :
    m α → (α → m β) → m β :=
  sorry

/-
## 2.9

Implement these functions by looking carefully at the type signatures of what you're given.
-/

def yoneda (f : Type u → Type v) [Functor f] (g : {β : Type u} → (α → β) → f β) : f α :=
  sorry

def yoneda' (f : Type u → Type v) [Functor f] (y : f α) : {β : Type u} → (α → β) → f β :=
  sorry

/-
## 2.10

Implement the function below that returns `42` if the input string is `"lean"` and otherwise leaves it unchanged. Since the type of this function is pretty complicated, we'll implement it using tactics mode, which isn't just for proofs!
-/

def lean_to_42_type (x : String) : Type :=
  if x = "lean" then ℕ else String

def lean_to_42 (x : String) : lean_to_42_type x := by
  sorry

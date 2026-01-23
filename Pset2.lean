import Mathlib

/-
# Pset 2

## 2.1

Prove the following lemmas in Lean.
-/

lemma two_plus_two : 2 + 2 = 4 := by
  simp

lemma and_swap : p ∧ q → q ∧ p := by
  intro h
  rw [and_comm] at h
  exact h

lemma add_rearrange {a b c d : ℝ} : 0 ≤ a + b + c + d ↔ -b - c ≤ a + d := by
  grind

lemma three_not_even {x : ℤ} : 2 * x ≠ 3 := by
  intro h
  apply_fun (· % 2) at h
  simp at h
  
lemma linear_arithmetic {a b c d e f : ℝ} :
    2 * a + b ≥ 1 →
    b ≥ 0 → c ≥ 0 → d ≥ 0 → e * f ≥ 0 →
    a ≥ 3 * c →
    c ≥ 6 * e * f → d - f * e * 5 ≥ 0 →
    a + b + 3 * c + d + 2 * e * f < 0 →
    False := by
  grind

lemma cross_multiply_field [Field α] {x y z w : α} :
    x / y = z / w →
    y ≠ 0 → w ≠ 0 →
    x * w = z * y := by
  grind

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
  grind

/-
## 2.2

Prove the following lemmas.
-/

lemma pow_two_larger : n ≤ 2 ^ n := by
  induction n <;> grind

lemma pow_two_larger' (h : 2 ≤ n) : (n - 2) * 2 ≤ 2 ^ (n - 1) := by
  let x := n - 2
  have : 0 <= x := by positivity
  have : n = x + 2 := by grind
  rw [this]
  simp
  suffices x <= 2^x by grind
  apply pow_two_larger


/-
## 2.3

Prove these lemmas about binary operations (taken from https//cjquines.com/files/binaryoperations.pdf).
-/

lemma cjq1 (f : α → α → α) (hl : ∀ x, f l x = x) (hr : ∀ x, f x r = x) : l = r := by
  have : f l r = l := by grind
  grind

lemma cjq2 (f : α → α → α) (h : ∀ x y, ∃ z, f x z = y ∧ ∀ z', f x z = f x z' → z = z')
    : ∃ g : α → α → α, ∀ x y, f x (g x y) = y ∧ g x (f x y) = y := by
  use fun x y => Classical.choose (h x y)
  grind

lemma cjq3 (f g : α → α → α) (hid : ∀ x, f i x = x ∧ f x i = x ∧ g j x = x ∧ g x j = x)
    (h : ∀ x y z w, f (g x y) (g z w) = g (f x z) (f y w)) : f = g := by
  have : i = j := by
    suffices f (g i j) (g j i) = i by grind
    grind
  suffices ∀ x y, g (f x i) (f i y) = g x y by grind
  grind

lemma cjq3' (f g : α → α → α) (hid : ∀ x, f i₁ x = x ∧ f x i₂ = x ∧ g j₁ x = x ∧ g x j₂ = x)
    (h : ∀ x y z w, f (g x y) (g z w) = g (f x z) (f y w)) : f = g := by
  have : i₁ = i₂ := by
    cases hid i₁
    grind
  have : j₁ = j₂ := by
    cases hid i₁
    grind
  let i := i₁
  let j := j₁
  have : i = j := by
    suffices f (g i j) (g j i) = i by grind
    grind
  suffices ∀ x y, g (f x i) (f i y) = g x y by grind
  grind

example (x : ℤ) : x % 2 != 0 ↔ ∃ k, x = 2 * k + 1 := by
  constructor
  · let d := x % 2
    intro
    have : d == 1 := by
      grind
    let q := (x - 1) / 2
    use q
    have : x = 2 * q + 1 := by grind
    grind
  · grind

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

Create a `structure` called `Color` to represent RGB colors. Then write a function that parses a [P6 PPM image](https://en.wikipedia.org/wiki/Netpbm#PPM_example) and returns an `Except` type with either an `Array (Array Color)` or an error message string. Prove that all array accesses are in bounds. Then, run your function on the file `image.ppm` using `IO.FS.readBinFile`.
-/

def parsePPM (bytes : ByteArray) := do
  sorry

/-
## 2.6

Create a new file called `Quine.lean` and add it as a `[[lean_exe]]` in the `lakefile.toml` file. Then write a [quine](https://en.wikipedia.org/wiki/Quine_(computing)) in Lean and run it with `lake exe`.

## 2.7

Give an example of a functor that isn't an applicative and an applicative that isn't a monad. For each example, determine which law is violated and prove it in Lean.
-/



/-
## 2.8

Another equivalent way to define monads is with a type class with a `fish` function of signature `(α → m β) → (β → m γ) → α → m γ`. Given this `fish` function, implement the other two equivalent formulations of monads.
-/

def joinFromFish (m : Type u → Type u) (fish : {α β γ : Type u} → (α → m β) → (β → m γ) → α → m γ) :
    m (m α) → m α :=
  sorry

def bindFromFish (m : Type u → Type u) (fish : {α β γ : Type u} → (α → m β) → (β → m γ) → α → m γ) :
    m α → (α → m β) → m β :=
  sorry

/-
## 2.9

Implement applicative `seq` for a monad, first without using `do` notation, and then simplify your implementation using `do`. Finally, prove that your `seq` function satisfies the applicative laws.
-/

namespace Monad

variable [Monad m] [LawfulMonad m]

def appSeq (fs : m (α → β)) (as : m α) : m β :=
  sorry

def appSeqDo (fs : m (α → β)) (as : m α) : m β := do
  sorry

infixl:60 " <*>' " => fun x y ↦ appSeq x y

lemma pure_seq (g : α → β) (x : m α) : pure g <*>' x = g <$> x := by
  sorry

lemma seq_pure (g : m (α → β)) (x : α) : g <*>' pure x = (· x) <$> g := by
  sorry

lemma seq_assoc (x : m α) (g : m (α → β)) (h : m (β → γ)) : h <*>' (g <*>' x) = (· ∘ ·) <$> h <*>' g <*>' x := by
  sorry

end Monad

/-
## 2.10

Show that the `Id'` type contructor below is an instance of `Monad` and `LawfulMonad`.
-/

def Id' (type : Type u) := type

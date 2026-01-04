#import "@preview/touying:0.6.1": *
#import themes.university: *

#show link: underline
#show: university-theme.with(
  aspect-ratio: "16-9",
  config-info(
    title: [Programs and Proofs],
    subtitle: [#image("img/lean_logo.svg", height: 50%)],
    author: [Anthony Wang (xy)],
    date: datetime.today(),
  ),
)
#show image: it => align(center, it)

#title-slide()

#outline(depth: 1)


Lean bio:
- Created in 2013 by Leo de Moura at Microsoft Research
- Lean 4 released in 2023, rewritten in Lean itself
- Named because it was supposed to be fast and minimal, not named after the drug
- A very modern programming language that enables building powerful abstractions





= Cool Lean projects

== Mathlib4

Mathlib4 (This is how everyone will be doing math in 20 years (maybe)) https://eric-wieser.github.io/mathlib-import-graph/ https://leanprover-community.github.io/mathlib_stats.html


== Video player
- Lean rickroll (You can choose your level of verification and safety)

== Rupert

https://www.youtube.com/watch?v=jDTPBdxmxKw

https://jcreedcmu.github.io/Noperthedron/blueprint/dep_graph_document.html


== SciLean

- https://lecopivo.github.io/scientific-computing-lean/Working-with-Arrays/Tensor-Operations/#Scientific-Computing-in-Lean--Working-with-Arrays--Tensor-Operations--Simple-Neural-Network (Blazingly fast and no GC)

== PhysLean

== Equational theories

- https://teorth.github.io/equational_theories/ "Math at web scale"


== Raytracer

https://github.com/kmill/lean4-raytracer

== Functorio

- https://github.com/konne88/functorio (If it compiles, it's most likely correct and bug-free)

== LeanTex

https://github.com/kiranandcode/LeanTeX/

== HouLean

https://github.com/lecopivo/HouLean

== Analysis

https://teorth.github.io/analysis/sec21/ (useful for teaching, instant feedback)

== Erdős 707

https://borisalexeev.com/pdf/erdos707.pdf (Maybe can solve the LLM hallucination problem, since LLMs suck at reasoning)

== Compile-time video player

- Lean rickroll in VSCode (Lean's metalanguage is just Lean)

== Insertion sort

#columns()[
  #text(size: 17pt)[
    ```lean
    variable [LE α] [DecidableLE α] [Std.IsLinearOrder α] [BEq α] [LawfulBEq α] (xs : List α)

    @[grind]
    def insert (a : α)
      | [] => [a]
      | x :: xs =>
        if a ≤ x then
          a :: x :: xs
        else
          x :: insert a xs

    @[grind]
    def insertionSort : List α → List α
      | [] => []
      | x :: xs => insert x (insertionSort xs)

    @[grind]
    def Sorted : List α → Prop
      | [] | [_] => True
      | x :: x' :: xs => x ≤ x' ∧ Sorted (x' :: xs)

    theorem insertCorrect x : (Sorted xs → Sorted (insert x xs)) ∧ (x :: xs).Perm (insert x xs) := by
      induction xs with
      | nil => grind
      | cons _ t => cases t <;> grind

    theorem insertionSortCorrect : Sorted (insertionSort xs) ∧ xs.Perm (insertionSort xs) := by
      induction xs with
      | nil => grind
      | cons h t => grind [insertCorrect (insertionSort t) h]
    ```
  ]
]

/*

Part 2 (30 mins): various random topics
- First-order logic
- Lambda calculus
- ADTs
- Pattern matching
- Polymorphism
- Functors
- Applicatives
- Monads
- IO
- do notation and local imperativity
- Type classes
- First-class propositions
- Total and partial functions (0/0)
- Dependent types
- Curry-Howard
- Tactics
- grind
- Induction and recursion
- Inductive types and GADTs
- Termination
- Universes (What is type of type?)
- Axioms
- Prop weirdness
- Unsafe Lean
- FFI

This looks super ambitious probably can only get through 20% of those topics

Discussion questions:
- Why types (in conventional programming languages)?
- Has anyone used a Python type checker or a statically typed programming language?
- What is a proof?
- What's the purpose of a proof? How do we know when a proof is correct?
- What does it mean for a program to be "correct" or "bug-free" and is this goal attainable?
- Is AI gonna replace human programmers?
- Is testing enough for real-world applications?

Probably should explain Curry-Howard and propositions as types, proofs as terms


Break in the middle


Part 3 (1 hour):

NNG4 maybe? Although I'm not a huge fan since it's kinda tedious

However with only 2 hours of experience you can only really prove easy and trivial stuff

Personally I'd feel a bit scammed if I signed up for a Lean class and only proved 2 + 2 = 4

https://adam.math.hhu.de/
https://adam.math.hhu.de/#/g/leanprover-community/nng4

https://lean-lang.org/install/


Resources:
- https://leanprover-community.github.io/documentation.html
- https://learnyouahaskell.com/chapters

*/

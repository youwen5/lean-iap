import LeanTeX

#latex_executable "lualatex"

#latex_preamble [|
  \title{Lean}
  \author{Anthony Wang (xy)}
|]

#latex_slide do
  latex![| \titlepage |]

#latex_slide "Example Slide" do
  \begin{itemize}
    \item{"Writing LaTeX-like code within Lean"}
    \item{"Looks like LaTeX"}
    \item{"is actually Lean~"}
  \end{itemize}
  latex![| $\mathsf{a}$ |]
  with steps [step1, step2, step3, step4] do
     latex![|
       \begin{tikzpicture}
          \draw<@{step1}->  (0,0) rectangle ++(1,1);
          \draw<@{step2}->  (1,0) rectangle ++(1,1);
          \draw<@{step3}->  (2,0) rectangle ++(1,1);
          \draw<@{step4}->  (3,0) rectangle ++(1,1);
       \end{tikzpicture}
     |]

#latex_slide "Testing" do
  latex![|
  |]


/-
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

= Cool Lean projects

// Instead of telling you how cool Lean is, let's look at some cool Lean projects
// It can do things that no other language in existence can do

- #link("https://github.com/kmill/lean4-raytracer")[Raytracer] // Can do general-purpose programming in Lean, fast and no GC
- #link("https://git.unnamed.website/leanime/tree/Leanime.lean")[Video player] // Lean's metalanguage is just Lean, can make the video player run at compile time too!
- #link("https://www.youtube.com/watch?v=jDTPBdxmxKw")[Rupert] // Machine-checked proofs
- #link("https://lecopivo.github.io/scientific-computing-lean/Working-with-Arrays/Tensor-Operations/#Scientific-Computing-in-Lean--Working-with-Arrays--Tensor-Operations--Simple-Neural-Network")[SciLean] // Dependently-typed tensor dimensions
- #link("https://teorth.github.io/equational_theories/paper.pdf")[Equational theories] // "Math at web scale"
- #link("https://codeberg.org/exozyme/ring3")[Webring generator] // Webdev using Lean!
- #link("https://github.com/konne88/functorio")[Functorio] // If it compiles, it's most likely correct and bug-free
- #link("https://github.com/lecopivo/HouLean")[HouLean] // Scripting language for Blender-like software
- #link("https://eric-wieser.github.io/mathlib-import-graph/")[Mathlib] // This is how everyone will be doing math in 20 years (maybe), 250k theorems, "community-driven effort to digitize mathematics"
- #link("https://teorth.github.io/analysis/sec21/")[Analysis] // Useful for teaching, instant feedback
- #link("https://borisalexeev.com/pdf/erdos707.pdf")[Erdős 707] // Maybe can solve the LLM hallucination problem, since LLMs suck at reasoning
- #link("https://github.com/kiranandcode/LeanTeX/")[LeanTeX] // Good for embedding DSLs


// Principia Mathematica
// Incompleteness theorems
// Images from those SIPB books
// ITPs vs ATPs
// Set theory (Mizar, Metamath)
// Simple type theory (Isabelle/HOL)
// Dependent type theory (Lean, Rocq, Agda, Idris)
// History
// Leo quote
// LinkedIn
// Not the drug


#slide[
  - A very new programming language and proof assistant that enables building powerful abstractions #pause

  - Extremely powerful type system, can encode almost all of math

  - Compiles to C, fast during runtime

  - 2013: Created by Leo de Moura at Microsoft #pause

  - 2023: Lean 4 released, rewritten in Lean itself
    - Except for the type checker which is in C++
]

// Named because it was supposed to be fast and minimal, not named after the drug


// https://cjquines.com/files/typetheory.pdf


/*


Discussion questions:
- Why types (in conventional programming languages)?
- Has anyone used a Python type checker or a statically typed programming language?
- What is a proof?
- What's the purpose of a proof? How do we know when a proof is correct?
- What does it mean for a program to be "correct" or "bug-free" and is this goal attainable?
- Is AI gonna replace human programmers?
- Is testing enough for real-world applications?

Probably should explain Curry-Howard and propositions as types, proofs as terms

*/

-/

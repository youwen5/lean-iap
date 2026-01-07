import LeanTeX

#latex_executable "lualatex"

#latex_preamble [|
  \usetheme{Madrid}
  \hypersetup{colorlinks=true}
  \title{Programs and Proofs}
  \subtitle{\includegraphics[scale=0.5]{lean_logo.png}}
  \author{Anthony Wang (xy)}
|]

#latex_slide do
  latex![| \titlepage |]

#latex_slide "Cool Lean projects" do
  -- Instead of telling you how cool Lean is, let's look at some cool Lean projects
  -- It can do things that no other language in existence can do
  \begin{itemize}
    -- Can do general-purpose programming in Lean, fast and no GC
    \item{"\\href{https://github.com/kmill/lean4-raytracer}{Raytracer}"}
    -- Lean's metalanguage is just Lean, can make the video player run at compile time too!
    \item{"\\href{https://git.unnamed.website/leanime/tree/Leanime.lean}{Video player}"}
    -- Machine-checked proofs
    \item{"\\href{https://www.youtube.com/watch?v=jDTPBdxmxKw}{Rupert}"}
    -- Dependently-typed tensor dimensions
    \item{"\\href{https://lecopivo.github.io/scientific-computing-lean/Working-with-Arrays/Tensor-Operations/\\#Scientific-Computing-in-Lean--Working-with-Arrays--Tensor-Operations--Simple-Neural-Network}{SciLean}"}
    -- "Math at web scale"
    \item{"\\href{https://teorth.github.io/equational_theories/paper.pdf}{Equational theories}"}
    -- Webdev using Lean!
    \item{"\\href{https://codeberg.org/exozyme/ring3}{Webring generator}"}
    -- If it compiles, it's most likely correct and bug-free
    \item{"\\href{https://github.com/konne88/functorio}{Functorio}"}
    -- Scripting language for Blender-like software
    \item{"\\href{https://github.com/lecopivo/HouLean}{HouLean}"}
    -- This is how everyone will be doing math in 20 years (maybe), 250k theorems, "community-driven effort to digitize mathematics"
    \item{"\\href{https://eric-wieser.github.io/mathlib-import-graph/}{Mathlib}"}
    -- Useful for teaching, instant feedback
    \item{"\\href{https://teorth.github.io/analysis/sec21/}{Analysis textbook}"}
    -- Maybe can solve the LLM hallucination problem, since LLMs suck at reasoning
    \item{"\\href{https://borisalexeev.com/pdf/erdos707.pdf}{Erdős 707}"}
    -- This presentation! Good for embedding DSLs
    \item{"\\href{https://github.com/kiranandcode/LeanTeX/}{LeanTeX}"}
  \end{itemize}

#latex_slide "History of formalized math" do
  \begin{itemize}
    \item{"1910: Principia Mathematica \\includegraphics{Principia_Mathematica_54-43.png}"}
    \item{"1931: Gödel's incompleteness theorems"}
  \end{itemize}

#latex_slide "History (cont.)" do
  \begin{itemize}
    \item{"1936: Entscheidungsproblem proven undecidable"}
    \item{"1956: Logic Theorist (\"first AI program\") \\includegraphics[scale=0.1]{lt.jpg}"} -- This book is in the SIPB library!
  \end{itemize}

#latex_slide "History (cont.)" do
  \begin{itemize}
    \item{"1976: Four color theorem proved using brute force (verified in Rocq in 2005)"} -- AKA Coq
    -- People were upset because proofs are about understanding, not correctness
  \end{itemize}

#latex_slide "ITPs vs ATPs" do
  \begin{itemize}
    \item{"Two main paradigms"}
    \item{"ITP = Interactive theorem prover, uses tactics, ex: Rocq, Lean"} -- Rocq used by FRAP
    \item{"ATP = Automated ..., uses SMT, ex: Dafny"} -- Dafny used by Verified SWE class
    \item{"ATPs are buggier, more brittle, require learning arcane SMT magic"}
  \end{itemize}

#latex_slide "Foundations" do
  \begin{itemize}
    \item{"Set theory (Mizar, Metamath)"}
    \item{"Simple type theory (Isabelle/HOL)"}
    \item{"Dependent type theory (Lean, Rocq, Agda, Idris)"}
  \end{itemize}
  -- https://mathoverflow.net/questions/376839/what-makes-dependent-type-theory-more-suitable-than-set-theory-for-proof-assista/376973#376973

#latex_slide "Lean bio" do
  \begin{itemize}
    \item{"2013: Created by Leo de Moura at Microsoft, previously created Z3"}
    \item{"2023: Lean 4 released, rewritten in Lean (except type checker)"} -- Type checker still in C++ for performance reasons
    \item{"Not named after the drug"} -- Allegedly the name is because it was supposed to be fast and minimal but it's not very minimal now
  \end{itemize}
  -- Also, Leo LinkedIn stuff and his famous quote

#latex_slide "Is Lean practical?" do
  \begin{itemize}
    \item{"\"Invisible math\" \\includegraphics[scale=0.5]{Vesica_piscis_circles.png}"}
    \item{"Automated tactics: grind, hammer, canonical"}
    \item{"AI: \\href{https://aristotle.harmonic.fun/}{Harmonic's Aristotle}, AlphaProof"}
  \end{itemize}

-- #latex_slide "Why Lean?" do
--   \begin{itemize}
--     \item{"Correctness"}
--     \item{"Refactoring math"}
--     \item{"Scalable"}
--     \item{"Fun!"}
--   \end{itemize}
-- https://www.imo.universite-paris-saclay.fr/~patrick.massot/files/exposition/why_formalize.pdf

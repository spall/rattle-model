
\begin{code}[hide]
open import Functional.State using (Oracle ; Cmd ; FileSystem)

module Functional.Build (oracle : Oracle) where

open import Data.List using (List ; [] ; _∷_)
open import Functional.State.Helpers (oracle) using (cmdReadNames ; cmdWriteNames ; run)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.Product using (_×_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
\end{code}

\newcommand{\build}{%
\begin{code}
Build : Set
Build = List Cmd
\end{code}}

\begin{code}[hide]
UniqueEvidence : Build → Build → List Cmd → Set
UniqueEvidence b₁ b₂ ls = Unique b₁ × Unique b₂ × Unique ls × Disjoint b₁ ls


data DisjointBuild : FileSystem -> Build -> Set where
  Null : ∀ {s} → DisjointBuild s []
  Cons : ∀ {s} x -> Disjoint (cmdReadNames x s) (cmdWriteNames x s) -> (b : Build) -> DisjointBuild (run x s) b -> DisjointBuild s (x ∷ b)


PreCond : FileSystem → Build → Build → Set
PreCond s br bc = DisjointBuild s br × Unique br × Unique bc × bc ↭ br
\end{code}

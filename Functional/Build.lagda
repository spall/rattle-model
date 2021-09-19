
\begin{code}[hide]
module Functional.Build where

open import Data.List using (List)
open import Functional.State using (Cmd)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.Product using (_×_)
\end{code}

\newcommand{\build}{%
\begin{code}
Build : Set
Build = List Cmd
\end{code}}

\begin{code}[hide]
UniqueEvidence : Build → Build → List Cmd → Set
UniqueEvidence b₁ b₂ ls = Unique b₁ × Unique b₂ × Unique ls × Disjoint b₁ ls
\end{code}

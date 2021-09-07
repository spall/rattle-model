
\begin{code}[hide]
module Functional.State where

open import Agda.Builtin.Equality
open import Data.Bool using (Bool ; if_then_else_)
open import Data.List using (List ; map ; foldr ; [] ; _∷_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ-syntax)
open import Data.String using (String ; _==_)
open import Data.String.Properties using (≡-setoid ; _≟_)
open import Functional.File using (File ; FileName ; FileContent ; Files ; FileNames)
open import Data.List.Membership.Setoid (≡-setoid) using (_∈_)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Relation.Binary.PropositionalEquality using (decSetoid ; trans ; sym ; subst)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈?_ ; _∉_)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Unary.Any using (here ; there ; tail)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
\end{code}

\newcommand{\sys}{%
\begin{code}
System : Set
System = FileName -> Maybe FileContent
\end{code}}

\newcommand{\cmd}{%
\begin{code}
Cmd : Set
Cmd = String
\end{code}}

\newcommand{\cmdF}{%
\begin{code}
CmdFunction : Set
CmdFunction = System → Files × Files
\end{code}}


\newcommand{\cmdP}{%
\begin{code}
reads : CmdFunction → System → FileNames
reads f s = map proj₁ (proj₁ (f s))

CmdProof : CmdFunction → Set
CmdProof f = ∀ s₁ s₂ → (∀ f₁ → f₁ ∈ reads f s₁ -> s₁ f₁ ≡ s₂ f₁)
           -> f s₁ ≡ f s₂ 
\end{code}}

\newcommand{\oracle}{%
\begin{code}
F : Set
F = Cmd -> Σ[ f ∈ CmdFunction ](CmdProof f)
\end{code}}

\newcommand{\mem}{%
\begin{code}
Memory : Set
Memory = List (Cmd × List (FileName × Maybe FileContent))
\end{code}}

\begin{code}[hide]
extend : File -> System -> System
extend (k , v) st = \ k₁ -> if (k == k₁) then just v else st k₁

read : List FileName -> System -> List (FileName × Maybe FileContent)
read fs sys = map (\ x -> (x , sys x)) fs
\end{code}

\begin{code}[hide]
save : Cmd -> List FileName -> System -> Memory -> Memory
save cmd files sys mm = (cmd , map (\f -> f , sys f) files) ∷ mm
\end{code}
\newcommand{\state}{%
\begin{code}
State : Set
State = (System × Memory)
\end{code}}

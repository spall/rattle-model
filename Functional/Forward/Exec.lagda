
\begin{code}[hide]
open import Functional.State using (State ; Oracle ; Cmd ; save ; FileSystem ; Memory ; extend)

module Functional.Forward.Exec (oracle : Oracle) where

open import Agda.Builtin.Equality
open import Functional.State.Helpers (oracle) as St using (cmdReadNames)
open import Data.Bool using (Bool ; if_then_else_)
open import Data.List using (List ; [] ; _∷_ ; map ; filter ; foldr ; _++_)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Data.Maybe as Maybe using (Maybe ; just ; decToMaybe ; is-nothing ; maybe ; nothing)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∃-syntax)
open import Function.Base using (_∘_)
open import Functional.File using (FileName ; FileContent ; Files)
open import Functional.Build (oracle) using (Build)
open import Relation.Nullary.Decidable.Core using (isNo)
open import Relation.Nullary.Negation using (¬?)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Data.List.Relation.Unary.All as All using (All ; all? ; lookup)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Relation.Binary.PropositionalEquality using (decSetoid ; trans ; sym ; subst ; cong)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Relation.Nullary using (yes ; no ; Dec)
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (Any-resp-⊆ ; ⊆-reflexive)

maybeAll : {sys : FileSystem} -> (ls : List (FileName × Maybe FileContent)) -> Maybe (All (λ (f₁ , v₁) → sys f₁ ≡ v₁) ls)
maybeAll {sys} ls = decToMaybe (g₁ ls)
  where g₁ : (ls : List (FileName × Maybe FileContent)) -> Dec (All (λ (f₁ , v₁) → sys f₁ ≡ v₁) ls)
        g₁ ls = all? (λ (f₁ , v₁) → ≡-dec _≟_ (sys f₁) v₁) ls

get : (x : Cmd) -> (ls : Memory) -> x ∈ map proj₁ ls -> List (FileName × Maybe FileContent)
get x ((x₁ , fs) ∷ ls) x∈ with x ≟ x₁
... | yes x≡x₁ = fs
... | no ¬x≡x₁ = get x ls (tail ¬x≡x₁ x∈)

run? : Cmd -> State -> Bool
run? cmd (sys , mm) with cmd ∈? map proj₁ mm
... | no cmd∉ = Bool.true
... | yes cmd∈ = is-nothing (maybeAll {sys} (get cmd mm cmd∈))

doRun : State -> Cmd -> State
doRun (sys , mm) cmd = let sys₂ = St.run cmd sys in
                           (sys₂ , save cmd (cmdReadNames cmd sys) sys₂ mm)
\end{code}

\newcommand{\runF}{%
\begin{code}
run : State -> Cmd -> State
run st cmd = if (run? cmd st)
               then doRun st cmd
               else st
\end{code}}

\newcommand{\forward}{%
\begin{code}
forward : State -> Build -> State
forward st [] = st
forward st (x ∷ b) = forward (run st x) b
\end{code}}

\begin{code}[hide]
{- Goal: prove if a command is in the memory, and the recorded files and the values of the files in the system are the same as the values in the memory, then
   running the command is equivalent to not running the command. 

 Or similarly/equivalently if a command is in the memory and the recorded files match what is in the system, then the files/values that the oracle says would be the output files, are already in the system. 

What does it mean for the command to be in the memory? The command is in the memory list, so it has
a corresponding list of files and maybe file contents, which in the case of the forward build, are
the files and their values read by the ocmmand when it was recorded as being run.  
-}
\end{code}

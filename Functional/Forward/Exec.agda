
open import Functional.State as St using (State ; F ; Cmd ; save ; System ; trace ; Memory ; extend)

module Functional.Forward.Exec (oracle : F) where

open import Agda.Builtin.Equality
open import Data.Bool using (Bool ; if_then_else_)
open import Data.List using (List ; [] ; _∷_ ; map ; filter ; foldr ; _++_)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Data.Maybe as Maybe using (Maybe ; just ; decToMaybe ; is-nothing ; maybe ; nothing)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∃-syntax)
open import Function.Base using (_∘_)
open import Functional.File using (FileName ; FileContent ; Files)
open import Functional.Build using (Build)
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

maybeAll : {sys : System} -> (ls : List (FileName × Maybe FileContent)) -> Maybe (All (λ (f₁ , v₁) → sys f₁ ≡ v₁) ls)
maybeAll {sys} ls = decToMaybe (g₁ ls)
  where g₁ : (ls : List (FileName × Maybe FileContent)) -> Dec (All (λ (f₁ , v₁) → sys f₁ ≡ v₁) ls)
        g₁ ls = all? (λ (f₁ , v₁) → ≡-dec _≟_ (sys f₁) v₁) ls

run? : Cmd -> State -> Bool
run? cmd (sys , mm) with mm cmd
... | nothing = Bool.true
... | just x = is-nothing (maybeAll {sys} x)

run : State -> Cmd -> State
run st cmd = if (run? cmd st)
               then (let sys = St.run oracle cmd (proj₁ st) in
                       (sys , save cmd (proj₁ (trace oracle (proj₁ st) cmd)) sys (proj₂ st)))
               else st


exec : State -> Build -> State
exec st [] = st
exec st (x ∷ b) = exec (run st x) b

{- Goal: prove if a command is in the memory, and the recorded files and the values of the files in the system are the same as the values in the memory, then
   running the command is equivalent to not running the command. 

 Or similarly/equivalently if a command is in the memory and the recorded files match what is in the system, then the files/values that the oracle says would be the output files, are already in the system. 

What does it mean for the command to be in the memory? The command is in the memory list, so it has
a corresponding list of files and maybe file contents, which in the case of the forward build, are
the files and their values read by the ocmmand when it was recorded as being run.  




-}

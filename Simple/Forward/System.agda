
module Forward.System where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Data.Bool using (Bool ; if_then_else_ ; true ; false)
open import Data.Maybe using (Maybe ; just ; nothing ; is-nothing)
open import Data.Maybe.Relation.Binary.Pointwise using (dec)
open import File using (File ; FileName ; FileContent)
open import State using (State)
open import Cmd using (Cmd ; _==_ ; run ; inputs ; outputFileNames)
open import Build using (Build)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-decSetoid ; _×ₛ_ ; ×-decidable)
open import Data.String.Properties using (≡-decSetoid ; _≟_)
open import Data.List.Base using (all)
open import Data.List.Membership.DecSetoid (×-decSetoid ≡-decSetoid ≡-decSetoid) using (_∈?_ ; _∈_)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable.Core using (isYes)
open import Data.List.Base using (map ; _++_)


{- Memory is a mapping from a command to the Files it read and wrote after it was run -}
Memory : Set
Memory = Cmd -> Maybe (List (FileName × Maybe FileContent))


empty : Memory
empty x = nothing

{- extend the memory with the outputs of the command
   extend the memory with the values of the input files
   from the state
-}
extend : Cmd -> State -> Memory -> Memory
extend x st mm = \x₂ -> if (x == x₂)
                        then just (map (\f -> f , st f) (inputs x ++ outputFileNames x))
                        else mm x₂


{- -}
unchanged? : Decidable _∈_
unchanged? = _∈?_


{- lookup command in memory, if its nothing; then false
   if its just ls then; for each thing in ls; see if it is the same in the st
   if anything in the st is different then false; else true
-} 
run? : Cmd -> State -> Memory -> Bool
run? x st mm with mm x
... | nothing = false
... | just x₁ = all (λ x₂ → let y = st (proj₁ x₂) in
                                 isYes (dec _≟_ (proj₂ x₂) y)) x₁

exec : State -> Memory -> Build -> (State × Memory)
exec st mm [] = st , mm
exec st mm (x ∷ b) = if (run? x st mm)
                     then (let st₂ = run x st in
                              exec st₂ (extend x st₂ mm) b)
                     else (exec st mm b)

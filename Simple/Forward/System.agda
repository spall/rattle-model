
module Forward.System where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Data.Bool using (Bool ; if_then_else_ ; true ; false)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Maybe.Relation.Binary.Pointwise using (dec)
open import File using (File ; FileName ; FileContent)
open import State using (State)
open import Cmd using (Cmd ; _==_ ; inputs ; outputFileNames)
open import Build using (Build)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Properties using (_≟_)
open import Data.List.Base using (all)
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


{- lookup command in memory, if its nothing; then false
   if its just ls then; for each thing in ls; see if it is the same in the st
   if anything in the st is different then false; else true
-} 
run? : Cmd -> State -> Memory -> Bool
run? x st mm with mm x
... | nothing = false
... | just x₁ = all (λ x₂ → let y = st (proj₁ x₂) in
                                 isYes (dec _≟_ (proj₂ x₂) y)) x₁

{- need to define run like this so Proofs.lemma1 and Proofs.lemma2 
   can be written like Build.lemma1 and Cmd.lemma2 -}
run : Cmd -> (State × Memory) -> (State × Memory)
run cmd (st , mm) = if (run? cmd st mm)
                    then (let st₂ = Cmd.run cmd st in
                             (st₂ , extend cmd st₂ mm))
                    else (st , mm)

{- same reason as above -}
exec : (State × Memory) -> Build -> (State × Memory)
exec p [] = p
exec p@(st , mm) (x ∷ b) = exec (run x p) b

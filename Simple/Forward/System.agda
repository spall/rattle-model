
module Forward.System where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Data.Bool using (Bool ; if_then_else_ ; true ; false)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing ; maybe)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Maybe.Relation.Binary.Pointwise using (dec)
open import File using (File ; FileName ; FileContent ; Files)
open import Function.Base using (_∘_)
open import State using (State)
open import Cmd using (Cmd ; _==_ ; inputs ; outputFileNames)
open import Build using (Build)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Data.List.Base using (any ; map ; _++_ ; filter ; foldr)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Relation.Nullary.Decidable.Core using (isNo ; isYes)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.Definitions using (Decidable)

open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)


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
                        then just (map (\f -> f , st f) (inputs x))
                        else mm x₂


{-  It is decidable what list of files are out of date in memory
    either it is the empty list; and we don't want to run the command
    or it is any other list (all equivalent) and we want to run the command
    or it is nothing and we want to run the command

  How do I define a decidable for this?

  We can decide whether something is nothing;
  we can decide whether something is just []
  therefore we can decide whether something is not just []

-}
changed? : State -> Memory -> Cmd -> Maybe (List FileName)
changed? st mm x = Maybe.map f (mm x)
  where f : List (FileName × Maybe FileContent) -> List FileName
        f = (map proj₁) ∘ (filter (λ x₁ → ¬? (dec _≟_ (proj₂ x₁) (st (proj₁ x₁))))) -- collect files that are not same as in state


run? : State -> Memory -> Cmd -> Bool
run? st mm x = isNo (dec _≡?_ (changed? st mm x) (just []))


{- need to define run like this so Proofs.lemma1 and Proofs.lemma2 
   can be written like Build.lemma1 and Cmd.lemma2 -}
{- run if run? returns a not just [] -}
run : Cmd -> (State × Memory) -> (State × Memory)
run cmd (st , mm) = if (run? st mm cmd)
                    then (let st₂ = Cmd.run cmd st in
                             (st₂ , extend cmd st₂ mm))
                    else (foldr State.extend st [] , mm)

{- same reason as above -}
exec : (State × Memory) -> Build -> (State × Memory)
exec p [] = p
exec p@(st , mm) (x ∷ b) = exec (run x p) b


filesWritten : Cmd -> State × Memory -> Files
filesWritten x (st , mm) = if (run? st mm x)
                           then Cmd.outputs x
                           else []
                           

fileNamesWritten : Cmd -> State × Memory -> List FileName
fileNamesWritten x (st , mm) = if (run? st mm x)
                               then outputFileNames x
                               else []
                               

filesRead : Cmd -> State × Memory -> List FileName
filesRead x (st , mm) = if (run? st mm x)
                        then inputs x
                        else []
                    


{- the memory contains no information for any cmd in the build -}
data freshBuild : Build -> State -> Memory -> Set where
  []  : {mm : Memory} {st : State} -> freshBuild [] st mm
  Cons : {st : State} {mm : Memory} -> (x : Cmd) -> (b : Build) -> (mm x ≡ nothing) -> (freshBuild b (Cmd.run x st) (extend x (Cmd.run x st) mm)) -> freshBuild (x ∷ b) st mm
  

data HazardFree : Build -> (State × Memory) -> List String -> Set where
  Null : {st-mm : State × Memory} {l : List String} -> HazardFree [] st-mm l -- empty build writes to nothing
  Cons : {st-mm : State × Memory} (c : Cmd) -> (b : Build) -> (l : List FileName) -> Disjoint (fileNamesWritten c st-mm) l -> HazardFree b (run c st-mm) ((fileNamesWritten c st-mm) ++ (filesRead c st-mm) ++ l) -> HazardFree (c ∷ b) st-mm l

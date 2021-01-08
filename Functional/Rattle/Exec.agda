
module Functional.Rattle.Exec where

open import Data.Bool using (Bool ; if_then_else_)
open import Data.List using (List ; [] ; _∷_ ; map ; filter ; _++_)
open import Data.String.Properties using (_≟_)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Data.Maybe as Maybe using (Maybe ; just)
open import Data.Maybe.Relation.Binary.Pointwise using (dec)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_)
open import Function.Base using (_∘_)
open import Functional.File using (FileName ; FileContent)
open import Functional.State as St using (State ; F ; Cmd ; save ; System ; trace)
open import Functional.Build using (Build)
open import Relation.Nullary.Decidable.Core using (isNo)
open import Relation.Nullary.Negation using (¬?)


changed? : Cmd -> State -> Maybe (List FileName)
changed? cmd (sys , mm) = Maybe.map f (mm cmd)
  where f : List (FileName × Maybe FileContent) -> List FileName
        f = (map proj₁) ∘ (filter (λ x₁ → ¬? (dec _≟_ (proj₂ x₁) (sys (proj₁ x₁)))))

run? : Cmd -> State -> Bool
run? cmd st = isNo (dec _≡?_ (changed? cmd st) (just []))

run : F -> State -> Cmd -> State
run f st cmd = if (run? cmd st)
               then (let sys = St.run f cmd (proj₁ st) in
                       let (rs , ws) = trace f (proj₁ st) cmd in
                         (sys , save cmd (rs ++ ws) sys (proj₂ st)))
               else st

exec : F -> State -> Build -> State
exec _ st [] = st
exec f st (x ∷ b) = exec f (run f st x) b

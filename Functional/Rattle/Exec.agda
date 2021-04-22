
open import Functional.State as St using (State ; F ; Cmd ; System ; trace ; save)

module Functional.Rattle.Exec (oracle : F) where

open import Data.Bool using (Bool ; if_then_else_)
open import Data.List using (List ; [] ; _∷_ ; map ; filter ; _++_)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Data.Maybe as Maybe using (Maybe ; just)
open import Data.Maybe.Relation.Binary.Pointwise using (dec)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_)
open import Function.Base using (_∘_)
open import Functional.File using (FileName ; FileContent)
open import Functional.Build using (Build)
open import Relation.Nullary.Decidable.Core using (isNo)
open import Relation.Nullary.Negation using (¬?)
open import Functional.Forward.Exec (oracle) using (run?)

doRun : State -> Cmd -> State
doRun (sys , mm) cmd = let sys₂ = St.run oracle cmd sys in
                           (sys₂ , save cmd ((proj₁ (trace oracle sys cmd)) ++ (proj₂ (trace oracle sys cmd))) sys₂ mm)

run : State -> Cmd -> State
run st cmd = if (run? cmd st)
             then doRun st cmd
             else st
             

exec : State -> Build -> State
exec st [] = st
exec st (x ∷ b) = exec (run st x) b

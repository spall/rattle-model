
module Functional.Script.Exec where

open import Data.List using ([] ; _∷_ ; List ; map ; _++_)
open import Data.Product using (proj₁ ; proj₂ ; _,_)
open import Functional.State using (F ; run ; System ; Cmd ; trace)
open import Functional.Build using (Build)
open import Functional.File using (FileName)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)

exec : F -> System -> Build -> System
exec _ sys [] = sys
exec f sys (x ∷ b) = exec f (run f x sys) b

writes : F -> System -> Build -> List FileName
writes _ _ [] = []
writes f sys (x ∷ b) = (proj₂ (trace f sys x)) ++ writes f (run f x sys) b

fs : F -> System -> Cmd -> List FileName
fs f sys c = let (rs , ws) = trace f sys c in
                rs ++ ws

data HazardFree : F -> System -> Build -> List FileName -> Set where
  Null : {f : F} {sys : System} {ls : List FileName} -> HazardFree f sys [] ls
  Cons : {f : F} {sys : System} (c : Cmd) -> (b : Build) -> (ls : List FileName) -> Disjoint (proj₂ (trace f sys c)) ls -> HazardFree f (run f c sys) b ((fs f sys c) ++ ls) -> HazardFree f sys (c ∷ b) ls

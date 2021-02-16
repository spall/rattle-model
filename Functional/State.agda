
module Functional.State where

open import Agda.Builtin.Equality
open import Data.Bool using (Bool ; if_then_else_)
open import Data.List using (List ; map ; foldr)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ-syntax)
open import Data.String using (String ; _==_)
open import Data.String.Properties using (≡-setoid)
open import Functional.File using (File ; FileName ; FileContent ; Files)
open import Data.List.Membership.Setoid (≡-setoid) using (_∈_)

System : Set
System = FileName -> Maybe FileContent

extend : File -> System -> System
extend (k , v) st = \ k₁ -> if (k == k₁) then just v else st k₁

Cmd : Set
Cmd = String

F : Set
F = Cmd -> Σ[ f ∈ (System -> Files × Files) ](∀ s s₁ → (∀ f₁ → f₁ ∈ map proj₁ (proj₁ (f s)) -> s f₁ ≡ s₁ f₁) -> f s ≡ f s₁)

read : List FileName -> System -> List (FileName × Maybe FileContent)
read fs sys = map (\ x -> (x , sys x)) fs

inputs : F -> System -> Cmd -> List FileName
inputs f sys cmd = map proj₁ (proj₁ (proj₁ (f cmd) sys))

trace : F -> System -> Cmd -> (List FileName × List FileName)
trace f sys cmd = let (rs , ws) = proj₁ (f cmd) sys in
                    (map proj₁ rs , map proj₁ ws)


run : F -> Cmd -> System -> System
run f cmd sys = foldr extend sys (proj₂ (proj₁ (f cmd) sys))

Memory : Set
Memory = Cmd -> Maybe (List (FileName × Maybe FileContent))

empty : Memory
empty x = nothing

save : Cmd -> List FileName -> System -> Memory -> Memory
save cmd files sys mm = \cmd₂ -> if (cmd == cmd₂)
                                 then just (map (\f -> f , sys f) files)
                                 else mm cmd₂

State : Set
State = (System × Memory) {- can add more later if needed -}



{-
data SysProp : System -> Build -> System -> Set where
  [] : {sys : System} SysProp sys [] sys
  A  : {f} {sys : System} (x : Cmd) -> (b : Build) 
-}

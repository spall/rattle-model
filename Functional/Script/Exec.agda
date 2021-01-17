
module Functional.Script.Exec where

open import Data.List using ([] ; _∷_ ; List ; map ; _++_)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∄-syntax ; ∃-syntax ; Σ-syntax)
open import Functional.State using (F ; run ; System ; Cmd ; trace)
open import Functional.Build using (Build)
open import Functional.File using (FileName)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Relation.Binary.PropositionalEquality using (decSetoid)
open import Data.String.Properties using (_≟_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_)
open import Relation.Nullary using (yes ; no)
open import Data.List.Relation.Unary.Any using (tail)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)

exec : F -> System -> Build -> System
exec _ sys [] = sys
exec f sys (x ∷ b) = exec f (run f x sys) b

writes : F -> System -> Build -> List FileName
writes _ _ [] = []
writes f sys (x ∷ b) = (proj₂ (trace f sys x)) ++ writes f (run f x sys) b

writesC : F -> System -> Cmd -> List FileName
writesC f sys x = proj₂ (trace f sys x)

readsC : F -> System -> Cmd -> List FileName
readsC f sys x = proj₁ (trace f sys x)

fs : F -> System -> Cmd -> List FileName
fs f sys c = let (rs , ws) = trace f sys c in
                rs ++ ws

{- gets the system that will be used when cmd is run as part of this build -}
getSys : F -> System -> (x : Cmd) -> (b : Build) -> x ∈ b -> System
getSys f sys x (x₁ ∷ b) x∈b with x ≟ x₁
... | yes p = sys
... | no ¬p = getSys f (run f x₁ sys) x b (tail ¬p x∈b)


data HazardFree : F -> System -> Build -> List FileName -> Set where
  Null : {f : F} {sys : System} {ls : List FileName} -> HazardFree f sys [] ls
  Cons : {f : F} {sys : System} (c : Cmd) -> (b : Build) -> (ls : List FileName) -> Disjoint (proj₂ (trace f sys c)) ls -> HazardFree f (run f c sys) b ((proj₁ (trace f sys c)) ++ (proj₂ (trace f sys c)) ++ ls) -> HazardFree f sys (c ∷ b) ls



{- hazards:  write-write 
             read-write
             speculative write-read: we have a reference build b; where x before y and y reads something x writes. 
                                     we have a re-ordered build b₂ ; which is also hazardfree in the above way
                                       it is a hazardfree re-ordering if ¬∃[ cmd ](cmd ∈ b₂ × ∃[ f ]( f ∈ writes cmd × ∃[ cmd₁ ](f ∈ reads cmd₁ × cmd₁ is after cmd in b₂ × cmd₁ is before cmd₂ in b)))

-}

¬speculate-wr-hazard : F -> System -> Build -> Build -> Set
¬speculate-wr-hazard f sys b b₂ = ∄[ x ](Σ[ x∈b₂ ∈ (x ∈ b₂) ](∃[ f₁ ](f₁ ∈ writesC f (getSys f sys x b₂ x∈b₂) x × ∃[ x₂ ](Σ[ x₂∈b₂ ∈ (x₂ ∈ b₂) ](f₁ ∈ readsC f (getSys f sys x₂ b₂ x₂∈b₂) x₂ × Σ[ x₂∈b ∈ (x₂ ∈ b) ](Σ[ x∈b ∈ (x ∈ b) ](∃[ f₂ ](f₂ ∈ writesC f (getSys f sys x₂ b x₂∈b) x₂ × f₂ ∈ readsC f (getSys f sys x b x∈b) x))))))))


{- b₂ is the re-ordering -}
data HazardFreeReordering : F -> System -> Build -> Build -> Set where
     HFR : {f : F} {sys : System} {ls : List FileName} (b : Build) -> (b₂ : Build) -> b ↭ b₂ -> HazardFree f sys b ls -> HazardFree f sys b₂ ls -> ¬speculate-wr-hazard f sys b b₂ -> HazardFreeReordering f sys b b₂

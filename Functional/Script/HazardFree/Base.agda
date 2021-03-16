
open import Functional.State using (F ; run ; System ; Cmd ; trace)

module Functional.Script.HazardFree.Base (oracle : F) where

open import Agda.Builtin.Equality
open import Common.List.Properties using (_before_en_)
open import Functional.Build using (Build)
open import Functional.File using (FileName)
open import Functional.Script.Exec (oracle) using (exec)
open import Relation.Binary.PropositionalEquality using (decSetoid)
open import Data.String.Properties using (_≟_)
open import Data.List using (List ; _++_ ; _∷_ ; [])
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.Product using (∃-syntax ; _×_ ; proj₁ ; proj₂ ; _,_)
open import Relation.Nullary using (¬_)

{- hazards:  write-write 
             read-write
             speculative write-read: we have a reference build b; where x before y and y reads something x writes. 
                                     we have a re-ordered build b₂ ; which is also hazardfree in the above way
                                       it is a hazardfree re-ordering if ¬∃[ cmd ](cmd ∈ b₂ × ∃[ f ]( f ∈ writes cmd × ∃[ cmd₁ ](f ∈ reads cmd₁ × cmd₁ is after cmd in b₂ × cmd₁ is before cmd₂ in b)))
-}


CmdWrites : System -> Cmd -> List FileName
CmdWrites s x = proj₂ (trace oracle s x)

CmdReads : System -> Cmd -> List FileName
CmdReads s x = proj₁ (trace oracle s x)

CmdReadWrites : System -> Cmd -> List FileName
CmdReadWrites s x = let (rs , ws) = trace oracle s x in
                        rs ++ ws

WriteBeforeRead : System -> Cmd -> Cmd -> Build -> Set
WriteBeforeRead s x₁ x₂ b = ∃[ f₁ ](∃[ xs ](∃[ ys ](∃[ zs ](b ≡ xs ++ x₁ ∷ ys ++ x₂ ∷ zs × f₁ ∈ CmdWrites (exec s xs) x₁ × f₁ ∈ CmdReads (exec s (xs ++ x₁ ∷ ys)) x₂))))

SpeculativeWRHazard : System -> Build -> Build -> Set
SpeculativeWRHazard s b₁ b₂ = ∃[ x₁ ](∃[ x₂ ](WriteBeforeRead s x₂ x₁ b₂ × x₁ before x₂ en b₁))

data HazardFree : System -> Build -> List FileName -> Set where
  Null : {s : System} {ls : List FileName} -> HazardFree s [] ls
  Cons : {s : System} (ls : List FileName) -> (c : Cmd) -> (b : Build) -> Disjoint (CmdWrites s c) ls -> HazardFree (run oracle c s) b ((CmdReadWrites s c) ++ ls) -> HazardFree s (c ∷ b) ls

data HazardFreeReordering : System -> Build -> Build -> Set where
 HFR : {s : System} {ls : List FileName} (b₁ : Build) -> (b₂ : Build) -> b₁ ↭ b₂ -> HazardFree s b₁ ls -> HazardFree s b₂ ls -> ¬ SpeculativeWRHazard s b₁ b₂ -> HazardFreeReordering s b₁ b₂


open import Functional.State using (F ; Cmd ; System ; trace ; run)

module Functional.Script.Hazard.Base (oracle : F) where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Nat.Properties as N using (1+n≢n)
open import Data.List using (List ; [] ; _∷_ ; _∷ʳ_  ; _++_ ; map ; foldl ; filter ; concatMap ; length)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_)
open import Data.Product.Properties using (,-injectiveˡ ; ,-injectiveʳ)
open import Functional.File using (FileName)
open import Functional.Build using (Build ; NBuild)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Common.List.Properties using (_before_en_)
open import Function using (_∘_)
open import Data.String.Properties using (_≟_)
open import Data.List.Relation.Unary.Any using (tail)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (concat⁺ ; map⁺ ; filter-⊆ ; filter⁺′ ; ++⁺)
open import Data.List.Relation.Unary.Any using (there ; here)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-decidable ; ≡×≡⇒≡)
open import Data.List.Relation.Binary.Equality.DecPropositional (_≟_) using (_≡?_)
open import Relation.Binary.PropositionalEquality using (subst ; cong ; sym ; trans)
open import Data.Empty using (⊥)


{- Hazards:

Do not depend on a reference order:

   Read before Write
   Write before Write

Does depend on a reference order:
  
  Speculative Write before Read


---------------------------------------

Goals (what we need):

execWError says there is either a hazard or a state

completeness takes evidence that the build has no hazards and proves that execWerror will return 
a state and not a hazard.  fundamentally this works by producing a contradiction when execWError
returns a hazard with the hazardfree evidence. 

What would be ideal is if hazard and hazardfree are set up in such a way that we can just say
contradiction 'hazard free evidnece' 'hazard evidence' without anymore manipulation

Existing hazardfree defs:

HazardFree is recursive and says the writes of the command at the head of the list are disjoint from the writes/reads that happened previously (exist in some list)

Would be nice to stick with this so i dont have to completely redo a lot of my proofs.  

HazardFreeReordering says 2 builds are permutations of one another. which could jsut be passed as its own argument to a function

Says both of the builds are hazardFree (by above def). 
And says there is not speculativewrhazard in the first of the 2 builds.  

speculativewrhazard says there are two commands, such that the first command is first in the original build, and the 2nd command writes to something before the first command in the build that is running.

this definition is just so long and ugly.  

-}
-- hazard needs to depend on the build.

-- the files a command read and wrote
FileInfo : Set
FileInfo = List ((Cmd × ℕ) × List FileName × List FileName)

getN : Cmd → FileInfo → ℕ
getN x [] = zero
getN x (x₁ ∷ fi) with x ≟ (proj₁ (proj₁ x₁))
... | yes x≡x₁ = suc (proj₂ (proj₁ x₁))
... | no ¬x≡x₁ = getN x fi

-- length (filter ((x ≟_) ∘ proj₁ ∘ proj₁) fi)

save : Cmd → List FileName → List FileName → FileInfo → FileInfo
save x rs ws fi = ((x , getN x fi) , rs , ws) ∷ fi

cmdsRun : FileInfo → List (Cmd × ℕ)
cmdsRun = map proj₁

filesRead : FileInfo → List FileName
filesRead = concatMap (proj₁ ∘ proj₂)

filesRead-⊆ : ∀ {xs} {ys} → xs ⊆ ys → filesRead xs ⊆ filesRead ys
filesRead-⊆ xs⊆ys = concat⁺ (map⁺ (proj₁ ∘ proj₂) xs⊆ys) 

filesWrote : FileInfo → List FileName
filesWrote = concatMap (proj₂ ∘ proj₂)

filesWrote-⊆ : ∀ {xs} {ys} → xs ⊆ ys → filesWrote xs ⊆ filesWrote ys
filesWrote-⊆ xs⊆ys = concat⁺ (map⁺ (proj₂ ∘ proj₂) xs⊆ys)

files : FileInfo → List FileName
files ls = (filesRead ls) ++ (filesWrote ls)

files-⊆ : ∀ {xs} {ys} → xs ⊆ ys → files xs ⊆ files ys
files-⊆ xs⊆ys = ++⁺ (filesRead-⊆ xs⊆ys) (filesWrote-⊆ xs⊆ys)

cmdWrote : FileInfo → (Cmd × ℕ) → List FileName
cmdWrote [] p = []
cmdWrote (x ∷ ls) p with ×-decidable _≟_ N._≟_ (proj₁ x) p
... | yes x≡p = proj₂ (proj₂ x)
... | no ¬x≡p = cmdWrote ls p

∈-cmdWrote∷ʳ : ∀ v x x₁ ls → v ∈ cmdWrote ls x₁ → ¬ (proj₁ x) ≡ x₁ → v ∈ cmdWrote (x ∷ ls) x₁
∈-cmdWrote∷ʳ v x x₁ ls v∈ ¬≡ with ×-decidable _≟_ N._≟_ (proj₁ x) x₁
... | yes x≡x₁ = contradiction (≡×≡⇒≡ x≡x₁) ¬≡
... | no ¬x≡x₁ = v∈

{-
cmdWrote-⊆ : ∀ x {xs} {ys} → xs ⊆ ys → cmdWrote xs x ⊆ cmdWrote ys x
cmdWrote-⊆ x xs⊆ys = concat⁺ (map⁺ (proj₂ ∘ proj₂) (filter⁺′ ((x ≟_) ∘ proj₁) ((x ≟_) ∘ proj₁) (λ x₄ → x₄) xs⊆ys))
-}

cmdRead : FileInfo → (Cmd × ℕ) → List FileName
cmdRead [] p = []
cmdRead (x ∷ ls) p with ×-decidable _≟_ N._≟_ (proj₁ x) p
... | yes x≡p = proj₁ (proj₂ x)
... | no ¬x≡p = cmdRead ls p

∈-cmdRead∷ˡ : ∀ v x ls → v ∈ proj₁ (proj₂ x) → v ∈ cmdRead (x ∷ ls) (proj₁ x)
∈-cmdRead∷ˡ v x ls v∈ with ×-decidable _≟_ N._≟_ (proj₁ x) (proj₁ x)
... | yes x≡x = v∈
... | no ¬x≡x = contradiction (refl , refl) ¬x≡x

cmdWrites : System → Cmd → List FileName
cmdWrites s x = proj₂ (trace oracle s x)

cmdReads : System → Cmd → List FileName
cmdReads s x = proj₁ (trace oracle s x)

{- We want to say that if commands read/wrote to the same files then they ran in the order the build says is ok.
 Aka If the 0th or 1st or 2nd x₁ doesn't appear before the 0th or 1st or 2nd x₂ then the
-}


{- ls is reversed; so last in ls was first run
  so if the command is later in ls it means it ran earlier.
  so if the reader is before the writer in ls, then the writer happened first
  
  The writer ran before the reader, but the write doesn't exist or the writer was after the reader in the original list. So 
-}
¬SpeculativeHazard : NBuild → FileInfo → Set
¬SpeculativeHazard b ls = ∀ x₁ x₂ → x₂ before x₁ en (cmdsRun ls) → ¬ x₁ before x₂ en b → Disjoint (cmdRead ls x₂) (cmdWrote ls x₁)

{- we have a Speculative hazard if a required command read something a speculative command wrote to. 
 So we need to be able to determine: 
1. when a command is required : a command is required if its the first command in the list?

2. when a command is speculated
-}

data Hazard : System → Cmd → NBuild → FileInfo → Set where
  ReadWrite   : ∀ s x {b} ls v → v ∈ (cmdWrites s x) → v ∈ (filesRead ls) → Hazard s x b ls
  WriteWrite  : ∀ s x {b} ls v → v ∈ (cmdWrites s x) → v ∈ (filesWrote ls) → Hazard s x b ls
  Speculative : ∀ s x b ls x₁ x₂ v → x₂ before x₁ en (cmdsRun (save x (cmdReads s x) (cmdWrites s x) ls)) → ¬ x₁ before x₂ en b → v ∈ cmdRead (save x (cmdReads s x) (cmdWrites s x) ls) x₂ → v ∈ cmdWrote (save x (cmdReads s x) (cmdWrites s x) ls) x₁ → Hazard s x b ls


hazardContradiction : ∀ s x b₂ ls → (hz : Hazard s x b₂ ls) → Disjoint (cmdWrites s x) (files ls) → ¬SpeculativeHazard b₂ (save x (cmdReads s x) (cmdWrites s x) ls) → ⊥
hazardContradiction s x b ls hz dsj ¬sh with hz
... | ReadWrite .s .x .ls v v∈cw v∈rs = contradiction (v∈cw , ∈-++⁺ˡ v∈rs) dsj
... | WriteWrite .s .x .ls v v∈cw v∈ws = contradiction (v∈cw , ∈-++⁺ʳ (filesRead ls) v∈ws) dsj
... | Speculative .s .x .b .ls x₁ x₂ v bf ¬bf v∈rs v∈ws = contradiction (v∈rs , v∈ws) (¬sh x₁ x₂ bf ¬bf)

data HazardFree : System → Build → NBuild → FileInfo → Set where
  [] : ∀ {s} {b} {ls} → HazardFree s [] b ls
  :: : ∀ s ls x b₁ b₂ → ¬SpeculativeHazard b₂ (save x (cmdReads s x) (cmdWrites s x) ls) → Disjoint (cmdWrites s x) (files ls) → HazardFree (run oracle x s) b₁ b₂ (save x (cmdReads s x) (cmdWrites s x) ls) → HazardFree s (x ∷ b₁) b₂ ls

{- No speculative hazards: 

for each command in the fileinfo, store its position in the rf build.... If the command we are running's position is 

1 2 3 4 5 6 7
A B C D B D A

1. we need to know the position of the command we are running in reference build
if we remove cmds from ref build as we go, then we just find the first cmd in the rf build that matches the one we're running and get it's number.
2. for each command in the fileinfo, if its number is bigger than the number of our new command; 
then the files those commands wrote to are disjoint from the files read by the current command??




-}


open import Functional.State using (F ; Cmd ; System ; trace ; run)

module Functional.Script.Hazard.Base (oracle : F) where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Nat.Properties as N using (1+n≢n ; ≤-refl ; ≤-step)
open import Data.Nat using (_>_)
open import Data.List using (List ; [] ; _∷_ ; _∷ʳ_  ; _++_ ; map ; foldl ; filter ; concatMap ; length ; concat)
open import Data.List.Properties using (concat-++ ; map-++-commute)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_ ; Σ-syntax) 
open import Data.Product.Properties using (,-injectiveˡ ; ,-injectiveʳ)
open import Functional.File using (FileName)
open import Functional.Build using (Build ; ΣNBuild ; Unique-> ; _¬≡-⊎->_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Common.List.Properties using (_before_en_)
open import Function using (_∘_)
open import Data.String.Properties using (_≟_)
open import Data.List.Relation.Unary.Any using (tail)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (concat⁺ ; map⁺ ; filter-⊆ ; filter⁺′ ; ++⁺)
open import Data.List.Relation.Unary.Any using (there ; here)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-decidable ; ≡×≡⇒≡)
open import Data.List.Relation.Binary.Equality.DecPropositional (_≟_) using (_≡?_)
open import Relation.Binary.PropositionalEquality using (subst ; cong ; sym ; trans)
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.AllPairs using (AllPairs ; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)


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

-- the files a command read and wrote ; and proof commands being added are "uniquely" labeled
FileInfo : Set
FileInfo = List (Cmd × List FileName × List FileName)

All⇒All : ∀ x n → (ls : List (Cmd × ℕ)) → All (_¬≡-⊎->_ (x , n)) ls → All (_¬≡-⊎->_ (x , suc n)) ls
All⇒All x n [] All.[] = All.[]
All⇒All x n (x₂ ∷ ls) (px All.∷ all) with x ≟ proj₁ x₂
... | no ¬x≡x₂ = inj₁ ¬x≡x₂ All.∷ All⇒All x n ls all 
... | yes x≡x₂ with px
... | inj₁ ¬x≡x₂ = contradiction x≡x₂ ¬x≡x₂
... | inj₂ n>sx₂ = inj₂ (≤-step n>sx₂) All.∷ All⇒All x n ls all

save : Cmd → List FileName → List FileName → FileInfo → FileInfo
save x rs ws fi = (x , rs , ws) ∷ fi

cmdsRun : FileInfo → List Cmd
cmdsRun = map proj₁

filesRead : FileInfo → List FileName
filesRead = concatMap (proj₁ ∘ proj₂)

∈-concatMap-++ : ∀ {v : FileName} f (xs : FileInfo) ys zs → v ∈ concatMap f (xs ++ zs) → v ∈ concatMap f (xs ++ ys ++ zs)
∈-concatMap-++ f xs ys zs v∈ with ∈-++⁻ (concat (map f xs)) (subst (λ x → _ ∈ x) ≡₁ v∈)
  where ≡₁ : concatMap f (xs ++ zs) ≡ concat (map f xs) ++ concat (map f zs)
        ≡₁ = trans (cong concat (map-++-commute f xs zs)) (sym (concat-++ (map f xs) (map f zs)))
... | inj₁ v∈xs = subst (λ x → _ ∈ x) ≡₁ (∈-++⁺ˡ v∈xs)
  where ≡₁ : concat (map f xs) ++ concat (map f (ys ++ zs)) ≡ concat (map f (xs ++ ys ++ zs))
        ≡₁ = trans (concat-++ (map f xs) (map f (ys ++ zs))) (cong concat (sym (map-++-commute f xs (ys ++ zs))))
... | inj₂ v∈ys = subst (λ x → _ ∈ x) ≡₁ (∈-++⁺ʳ (concat (map f xs)) (∈-++⁺ʳ (concat (map f ys)) v∈ys))
  where ≡₁ : concat (map f xs) ++ concat (map f ys) ++ concat (map f zs) ≡ concat (map f (xs ++ ys ++ zs))
        ≡₁ = trans (cong (concat (map f xs) ++_) (concat-++ (map f ys) (map f zs)))
                   (trans (concat-++ (map f xs) (map f ys ++ map f zs))
                          (cong concat (trans (cong (map f xs ++_) (sym (map-++-commute f ys zs)))
                                       (sym (map-++-commute f xs (ys ++ zs))))))


∈-filesRead-++ : ∀ {v} xs ys zs → v ∈ filesRead (xs ++ zs) → v ∈ filesRead (xs ++ ys ++ zs)
∈-filesRead-++ = ∈-concatMap-++ (proj₁ ∘ proj₂)

filesWrote : FileInfo → List FileName
filesWrote = concatMap (proj₂ ∘ proj₂)

∈-filesWrote-++ : ∀ {v} xs ys zs → v ∈ filesWrote (xs ++ zs) → v ∈ filesWrote (xs ++ ys ++ zs)
∈-filesWrote-++ = ∈-concatMap-++ (proj₂ ∘ proj₂)

files : FileInfo → List FileName
files ls = (filesRead ls) ++ (filesWrote ls)

∈-files-++ : ∀ {v} xs ys zs → v ∈ files (xs ++ zs) → v ∈ files (xs ++ ys ++ zs)
∈-files-++ xs ys zs v∈files with ∈-++⁻ (filesRead (xs ++ zs)) v∈files
... | inj₁ v∈reads = ∈-++⁺ˡ (∈-filesRead-++ xs ys zs v∈reads)
... | inj₂ v∈writes = ∈-++⁺ʳ (filesRead (xs ++ ys ++ zs)) (∈-filesWrote-++ xs ys zs v∈writes)

cmdWrote : FileInfo → Cmd → List FileName
cmdWrote [] p = []
cmdWrote (x ∷ ls) p with (proj₁ x) ≟ p
... | yes x≡p = proj₂ (proj₂ x)
... | no ¬x≡p = cmdWrote ls p


cmdWrote∷-≡ : ∀ x ls → cmdWrote (x ∷ ls) (proj₁ x) ≡ proj₂ (proj₂ x)
cmdWrote∷-≡ x ls with (proj₁ x) ≟ (proj₁ x)
... | yes x≡x = refl
... | no ¬x≡x = contradiction refl ¬x≡x

∈-cmdWrote∷ : ∀ {v} x x₁ ls → v ∈ cmdWrote ls x₁ → ¬ (proj₁ x) ≡ x₁ → v ∈ cmdWrote (x ∷ ls) x₁
∈-cmdWrote∷ x x₁ ls v∈ ¬≡ with (proj₁ x) ≟ x₁
... | yes x≡x₁ = contradiction x≡x₁ ¬≡
... | no ¬x≡x₁ = v∈

-- if there is a file in the cmdRead for x , then x ∈ xs
lemma2 : ∀ {v} x xs → v ∈ cmdWrote xs x → x ∈ map proj₁ xs
lemma2 x (x₁ ∷ xs) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = here (sym x₁≡x)
... | no ¬x₁≡x = there (lemma2 x xs v∈)

∈-cmdWrote++⁺ʳ : ∀ {v} x xs ys → Unique (map proj₁ (xs ++ ys)) → v ∈ cmdWrote ys x → v ∈ cmdWrote (xs ++ ys) x
∈-cmdWrote++⁺ʳ x [] ys u v∈ = v∈
∈-cmdWrote++⁺ʳ x (x₁ ∷ xs) ys (px₁ ∷ u) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = contradiction x₁≡x (lookup px₁ x∈xs++ys)
  where x∈xs++ys : x ∈ map proj₁ (xs ++ ys)
        x∈xs++ys = subst (λ ls → _ ∈ ls) (sym (map-++-commute proj₁ xs ys)) (∈-++⁺ʳ (map proj₁ xs) (lemma2 x ys v∈))
... | no ¬x₁≡x = ∈-cmdWrote++⁺ʳ x xs ys u v∈

∈-cmdWrote++mid : ∀ {v} x xs ys zs → Unique (map proj₁ (xs ++ ys ++ zs)) → v ∈ cmdWrote (xs ++ zs) x → v ∈ cmdWrote (xs ++ ys ++ zs) x
∈-cmdWrote++mid x [] ys zs u v∈ = ∈-cmdWrote++⁺ʳ x ys zs u v∈
∈-cmdWrote++mid x (x₁ ∷ xs) ys zs (px₁ ∷ u) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = v∈
... | no ¬x₁≡x = ∈-cmdWrote++mid x xs ys zs u v∈



cmdRead : FileInfo → Cmd → List FileName
cmdRead [] p = []
cmdRead (x ∷ ls) p with (proj₁ x) ≟ p
... | yes x≡p = proj₁ (proj₂ x)
... | no ¬x≡p = cmdRead ls p

∈-cmdRead∷l : ∀ {v} x ls → v ∈ proj₁ (proj₂ x) → v ∈ cmdRead (x ∷ ls) (proj₁ x)
∈-cmdRead∷l x ls v∈ with (proj₁ x) ≟ (proj₁ x)
... | no ¬x≡x = contradiction refl ¬x≡x
... | yes x≡x = v∈

∈-cmdRead∷ : ∀ {v} x x₁ ls → v ∈ cmdRead ls x₁ → ¬ (proj₁ x) ≡ x₁ → v ∈ cmdRead (x ∷ ls) x₁
∈-cmdRead∷ x x₁ ls v∈ ¬≡ with (proj₁ x) ≟ x₁
... | yes x≡x₁ = contradiction x≡x₁ ¬≡
... | no ¬x≡x₁ = v∈

-- if there is a file in the cmdRead for x , then x ∈ xs
lemma1 : ∀ {v} x xs → v ∈ cmdRead xs x → x ∈ map proj₁ xs
lemma1 x (x₁ ∷ xs) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = here (sym x₁≡x)
... | no ¬x₁≡x = there (lemma1 x xs v∈)

∈-cmdRead++⁺ʳ : ∀ {v} x xs ys → Unique (map proj₁ (xs ++ ys)) → v ∈ cmdRead ys x → v ∈ cmdRead (xs ++ ys) x
∈-cmdRead++⁺ʳ x [] ys u v∈ = v∈
∈-cmdRead++⁺ʳ x (x₁ ∷ xs) ys (px₁ ∷ u) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = contradiction x₁≡x (lookup px₁ x∈xs++ys)
  where x∈xs++ys : x ∈ map proj₁ (xs ++ ys)
        x∈xs++ys = subst (λ ls → _ ∈ ls) (sym (map-++-commute proj₁ xs ys)) (∈-++⁺ʳ (map proj₁ xs) (lemma1 x ys v∈))
... | no ¬x₁≡x = ∈-cmdRead++⁺ʳ x xs ys u v∈

∈-cmdRead++mid : ∀ {v} x xs ys zs → Unique (map proj₁ (xs ++ ys ++ zs)) → v ∈ cmdRead (xs ++ zs) x → v ∈ cmdRead (xs ++ ys ++ zs) x
∈-cmdRead++mid x [] ys zs u v∈ = ∈-cmdRead++⁺ʳ x ys zs u v∈
∈-cmdRead++mid x (x₁ ∷ xs) ys zs (px₁ ∷ u) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = v∈
... | no ¬x₁≡x = ∈-cmdRead++mid x xs ys zs u v∈

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


Write ran before read, but Writer should have run AFTER reader.  
-}
¬SpeculativeHazard : Build → FileInfo → Set
¬SpeculativeHazard b ls = ∀ x₁ x₂ → x₂ before x₁ en (cmdsRun ls) → x₂ ∈ b → ¬ x₁ before x₂ en b → Disjoint (cmdRead ls x₂) (cmdWrote ls x₁)

{- if ; reader is after the writer (in the run)

   but the reader is before the writer in the real build; then the reads/writes must be disjoint. 

   reader is before the writer; or the writer is not in the build.

 -- 
  
(A , 3) (C , 0) (A , 2) (B , 0) (A , 1)  (D, 0) (A , 0)   

what if we end up not running (A , 1)





-}

{- we have a Speculative hazard if a required command read something a speculative command wrote to. 
 So we need to be able to determine: 
1. when a command is required : a command is required if its the first command in the list?

2. when a command is speculated
-}

data Hazard : System → Cmd → Build → FileInfo → Set where
  ReadWrite   : ∀ s x {b} ls v → v ∈ (cmdWrites s x) → v ∈ (filesRead ls) → Hazard s x b ls
  WriteWrite  : ∀ s x {b} ls v → v ∈ (cmdWrites s x) → v ∈ (filesWrote ls) → Hazard s x b ls
  Speculative : ∀ s x b ls x₁ x₂ v → x₂ before x₁ en (cmdsRun (save x (cmdReads s x) (cmdWrites s x) ls)) → x₂ ∈ b → ¬ x₁ before x₂ en b → v ∈ cmdRead (save x (cmdReads s x) (cmdWrites s x) ls) x₂ → v ∈ cmdWrote (save x (cmdReads s x) (cmdWrites s x) ls) x₁ → Hazard s x b ls


hazardContradiction : ∀ s x b₂ ls → (hz : Hazard s x b₂ ls) → Disjoint (cmdWrites s x) (files ls) → ¬SpeculativeHazard b₂ (save x (cmdReads s x) (cmdWrites s x) ls) → ⊥
hazardContradiction s x b ls hz dsj ¬sh with hz
... | ReadWrite .s .x .ls v v∈cw v∈rs = contradiction (v∈cw , ∈-++⁺ˡ v∈rs) dsj
... | WriteWrite .s .x .ls v v∈cw v∈ws = contradiction (v∈cw , ∈-++⁺ʳ (filesRead ls) v∈ws) dsj
... | Speculative .s .x .b .ls x₁ x₂ v bf x₂∈b ¬bf v∈rs v∈ws = contradiction (v∈rs , v∈ws) (¬sh x₁ x₂ bf x₂∈b ¬bf)

data HazardFree : System → Build → Build → FileInfo → Set where
  [] : ∀ {s} {b} {ls} → HazardFree s [] b ls
  :: : ∀ s ls x b₁ b₂ → ¬SpeculativeHazard b₂ (save x (cmdReads s x) (cmdWrites s x) ls) → Disjoint (cmdWrites s x) (files ls) → HazardFree (run oracle x s) b₁ b₂ (save x (cmdReads s x) (cmdWrites s x) ls) → HazardFree s (x ∷ b₁) b₂ ls

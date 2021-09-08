{-# OPTIONS --allow-unsolved-metas #-}

open import Functional.State as St using (F ; System ; Cmd ; extend ; read ; Memory)

module Functional.Script.Proofs (oracle : F) where

open import Agda.Builtin.Equality
open import Functional.State.Helpers (oracle) using (cmdWriteNames ; run ; cmdReadNames)
open import Functional.Script.Exec (oracle) using (exec ; buildWriteNames)
open import Functional.Script.Hazard (oracle) using (HazardFree ; FileInfo)
open import Functional.Script.Hazard.Properties (oracle) using (hf-∷ʳ-l ; hf-drop-mid)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List using (_∷ʳ_ ; List)
open import Data.List.Properties using (unfold-reverse ; reverse-involutive ; ++-identityʳ ; length-reverse)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_ ; ↭-sym ; ↭-refl ; ↭-trans)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (Any-resp-↭ ; drop-mid ; ↭-length ; ∈-resp-↭ ; ++↭ʳ++)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique ; _∷_ ; head ; tail ; [])
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (++⁺)
open import Data.List using (map ; reverse ; length ; [] ; _∷_ ; _++_ ; [_])
open import Data.Product using (proj₁ ; proj₂ ; _,_)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-∃++ ; ∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any as Any using (here ; there)
open import Data.List.Relation.Unary.Any.Properties using (reverse⁺)
open import Relation.Binary.PropositionalEquality using (subst ; subst₂ ; sym ; trans)
open import Data.List.Relation.Unary.All as All using (All ; _∷_)
open import Data.List.Relation.Unary.All.Properties as AllP hiding (++⁺)
open import Relation.Nullary using (¬_)
open import Functional.Build using (Build)
open import Functional.Script.Properties (oracle) using (exec-f₁≡ ; exec-≡f₁ ; writes≡)
open import Functional.Rattle.Exec (oracle) using (UniqueEvidence)

{- If we follow the concept of hazardfree, it doesn't make sense, for 
  a hazardfree build to contain duplicates because those commands would need to do the
same thing, which would cause a hazard. + rattle doesn't run duplicates, so ....
lets just assume builds are unique. make my life easier...-}
all-drop-mid : ∀ (xs : Build) {ys} {x} {x₁} → All (λ y → ¬ x₁ ≡ y) (xs ++ x ∷ ys) → All (λ y → ¬ x₁ ≡ y) (xs ++ ys)
all-drop-mid [] all₁ = All.tail all₁
all-drop-mid (x₂ ∷ xs) all₁ = (All.head all₁) ∷ (all-drop-mid xs (All.tail all₁))

unique-drop-mid : ∀ (xs : Build) {ys} {x} → Unique (xs ++ x ∷ ys) → Unique (xs ++ ys)
unique-drop-mid [] (x₁ ∷ u) = u
unique-drop-mid (x₁ ∷ xs) u = (all-drop-mid xs (head u)) ∷ (unique-drop-mid xs (tail u))

unique→disjoint : ∀ {x₁ : Cmd} xs → All (λ y → ¬ x₁ ≡ y) xs → Disjoint xs (x₁ ∷ [])
unique→disjoint [] All.[] = λ ()
unique→disjoint (x ∷ xs) (¬x₁≡x ∷ all₁) x₂ = unique→disjoint xs all₁ (Any.tail (λ v≡x → ¬x₁≡x (trans (g₁ (proj₂ x₂)) v≡x)) (proj₁ x₂) , proj₂ x₂)
  where g₁ : ∀ {v} {x₁} → v ∈ x₁ ∷ [] → x₁ ≡ v
        g₁ (here px) = sym px

all-reverse : ∀ {x₁ : Cmd} xs → All (λ y → ¬ x₁ ≡ y) xs → All (λ y → ¬ x₁ ≡ y) (reverse xs)
all-reverse [] All.[] = All.[]
all-reverse (x ∷ xs) (px ∷ all₁) = subst (λ x₂ → All (λ y → ¬ _ ≡ y) x₂) (sym (unfold-reverse x xs)) (AllP.++⁺ (all-reverse xs all₁) (px ∷ All.[]))

unique-reverse : ∀ xs → Unique xs → Unique (reverse xs)
unique-reverse [] u = []
unique-reverse (x₁ ∷ xs) (px ∷ u) with ++⁺ (unique-reverse xs u) (All.[] ∷ []) (unique→disjoint (reverse xs) (all-reverse xs px))
... | u₁ = subst (λ ls → Unique ls) (sym (unfold-reverse x₁ xs)) u₁

-- we are adding x back and we need to prove its still the same.
-- how did we do this before??????????
lemma1 : ∀ {s} {b₁} {xs} {ys} {x} → (∀ f₁ → exec s (reverse b₁) f₁ ≡ exec s (xs ++ ys) f₁) → (∀ f₁ → exec s (reverse (x ∷ b₁)) f₁ ≡ exec s (xs ++ x ∷ ys) f₁)
lemma1 {s} {b₁} {xs} {ys} {x} ∀₁ f₁ = subst (λ x₁ → exec s x₁ f₁ ≡ exec s (xs ++ x ∷ ys) f₁)
                                            (sym (unfold-reverse x b₁))
                                            (exec-f₁≡ s f₁ x (reverse b₁) xs ys ∀₁ {!!} {!!} {!!})

{- length equivalence just makes the proof smaller -}
-- all of those unique and disjoint things are called UniqueEvidence now so replace to make it look better.
reordered-inner : ∀ {s} b₁ b₂ ls → {length b₁ ≡ length b₂} → b₁ ↭ b₂ → UniqueEvidence b₂ b₁ (map proj₁ ls) → HazardFree s (reverse b₁) [] ls → HazardFree s b₂ (reverse b₁) ls → (∀ f₁ → exec s (reverse b₁) f₁ ≡ exec s b₂ f₁)
reordered-inner [] [] ls ↭₁ (ub₂ , ub₁ , uls , dsj) hf₁ hf₂ = λ f₁ → refl
{- we remove x from both builds ; 
   then show adding x back in gives us equivalent system still -}
reordered-inner {s} (x ∷ b₁) b₂ ls ↭₁ (ub₂ , (px ∷ ub₁) , uls , dsj) hf hf₂ with ∈-∃++ (Any-resp-↭ ↭₁ (here refl)) -- find x in b₂
... | xs , ys , b₂≡xs++x∷ys with reordered-inner b₁ (xs ++ ys) ls {↭-length ↭₂} ↭₂ ((unique-drop-mid xs ub₃) , ub₁ , uls , dsj₂) hf₃ hf₄
  where ↭₂ : b₁ ↭ xs ++ ys
        ↭₂ = drop-mid [] xs (subst (λ x₁ → x ∷ b₁ ↭ x₁) b₂≡xs++x∷ys ↭₁)
        ub₃ : Unique (xs ++ x ∷ ys)
        ub₃ = subst (λ x₁ → Unique x₁) b₂≡xs++x∷ys ub₂
        dsj₂ : Disjoint (xs ++ ys) (map proj₁ ls)
        dsj₂ y with ∈-++⁻ xs (proj₁ y)
        ... | inj₁ v∈xs = dsj (subst (λ x₁ → _ ∈ x₁) (sym b₂≡xs++x∷ys) (∈-++⁺ˡ v∈xs) , proj₂ y)
        ... | inj₂ v∈ys = dsj (subst (λ x₁ → _ ∈ x₁) (sym b₂≡xs++x∷ys) (∈-++⁺ʳ xs (there v∈ys)) , proj₂ y)
        hf₃ : HazardFree s (reverse b₁) [] ls
        hf₃ = hf-∷ʳ-l (reverse b₁) (subst (λ x₁ → HazardFree s x₁ [] ls) (unfold-reverse x b₁) hf)
        ub₄ : Unique (reverse b₁ ∷ʳ x)
        ub₄ = subst (λ x₁ → Unique x₁) (unfold-reverse x b₁) (unique-reverse (x ∷ b₁) (px ∷ ub₁))
        hf₄ : HazardFree s (xs ++ ys) (reverse b₁) ls
        hf₄ = hf-drop-mid xs ys (reverse b₁) (λ x₁ → x₂∈ x₁) ub₃ ub₄ uls (subst (λ x₁ → Disjoint x₁ _) b₂≡xs++x∷ys dsj) (subst₂ (λ x₁ x₂ → HazardFree s x₁ x₂ ls) b₂≡xs++x∷ys (unfold-reverse x b₁) hf₂)
              where x₂∈ : ∀ {x₂} → x₂ ∈ xs ++ x ∷ ys → x₂ ∈ reverse b₁ ∷ʳ x
                    x₂∈ x₂∈₁ with subst (λ x₁ → _ ∈ x₁) (sym b₂≡xs++x∷ys) x₂∈₁
                    ... | a with ∈-resp-↭ (↭-sym ↭₁) a
                    ... | a₂ with reverse⁺ a₂
                    ... | a₃ = subst (λ x₁ → _ ∈ x₁) (unfold-reverse x b₁) a₃
        -- add back x.
... | ∀₁ = λ f₁ → subst₂ (λ x₁ x₂ → exec s x₁ f₁ ≡ exec s x₂ f₁)
                                            (sym (unfold-reverse x b₁)) (sym b₂≡xs++x∷ys)
                                            (exec-f₁≡ s f₁ x (reverse b₁) xs ys ∀₁ ≡₁ {!!} dsj₁)
          -- need to prove x does the same thing in both builds.
    where dsj₁ : Disjoint (cmdWriteNames x (exec s xs)) (buildWriteNames (run x (exec s xs)) ys)
          dsj₁ = {!!}
          dsj₃ : Disjoint (cmdReadNames x (exec s xs)) (buildWriteNames (run x (exec s xs)) ys)
          dsj₃ = {!!}
          ≡₂ : buildWriteNames (run x (exec s xs)) ys ≡ buildWriteNames (exec s xs) ys
          ≡₂ = writes≡ (run x (exec s xs)) (exec s xs) ys {!!}
          dsj₂ : Disjoint (cmdReadNames x (exec s xs)) (buildWriteNames (exec s xs) ys)
          dsj₂ = subst (λ x₁ → Disjoint (cmdReadNames x (exec s xs)) x₁) ≡₂ dsj₃
          ≡₁ : proj₁ (oracle x) (exec s (reverse b₁)) ≡ proj₁ (oracle x) (exec s xs)
          ≡₁ = sym (proj₂ (oracle x) (exec s xs) (exec s (reverse b₁))
               λ f₁ x₁ → trans (exec-≡f₁ s f₁ xs ys λ x₂ → dsj₂ (x₁ , x₂)) (sym (∀₁ f₁)))

{- Goal: Disjoint (cmdReadNames x (exec s xs)) (buildWriteNames (exec s xs) ys)
 We know: Disjoint (cmdReadNames x (exec s xs)) (buildWriteNames (run x (exec s xs)) ys)
          Disjoint (cmdWriteNames x (exec s xs)) (buildReadNames (run x (exec s xs)) ys)

new Goal : buildWriteNames (run x (exec s xs)) ys ≡ buildWriteNames (exec s xs) ys

Other goal: exec s xs f₁ ≡ exec s (xs ++ ys) f₁ ; where f₁ ∈ reads of x 
-- this should be true if f₁ not in the writes of ys. 
-- we know 

-- deeply annoying that holes 5 and 6 are not filled by the same thing; since they are very similar
-}

{- 
(exec-f₁≡ s f₁ x (reverse b) ls₁ ls₂ ∀₂ ≡₂ all₁ dsj)
                       
          where ∀₂ : (∀ f₂ → S.exec s (reverse b) f₂ ≡ S.exec s (ls₁ ++ ls₂) f₂)
                ∀₂ = subst (λ x₁ → ∀ f₂ → _ ≡ S.exec s x₁ f₂) (reverse-involutive (ls₁ ++ ls₂)) ∀₁
                hf₃ : {xs : List String} (s : System) (x : Cmd) (ls₁ ls₂ : Build) -> HazardFree s (ls₁ ++ x ∷ ls₂) xs -> HazardFree (S.exec s ls₁) (x ∷ ls₂) (S.build-rws s ls₁ xs)
                hf₃ s x [] ls₂ hf = hf
                hf₃ s x (x₁ ∷ ls₁) ls₂ (Cons _ .x₁ .(ls₁ ++ x ∷ ls₂) x₂ hf)
                  = hf₃ (run oracle x₁ s) x ls₁ ls₂ hf
                dsj : Disjoint (S.Cwrites (S.exec s ls₁) x) (writes (run oracle x (S.exec s ls₁)) ls₂)
                dsj = hf→disjointWrites (S.exec s ls₁) x ls₂ (hf₃ s x ls₁ ls₂ (subst (λ x₄ → HazardFree s x₄ _) reverse-b₁≡ls₁++x∷ls₂ hf₂))
                dsj₁ : Disjoint (S.Creads (S.exec s ls₁) x) (writes (S.exec s ls₁) ls₂)
                dsj₁ = still-disjoint (S.exec s ls₁) x ls₂
                       (hfr→disjoint s x (reverse b) ls₁ ls₂ hfr₁)
                       (hf→disjointReads (S.exec s ls₁) x ls₂ (hf₃ s x ls₁ ls₂ (subst (λ x₄ → HazardFree s x₄ _) reverse-b₁≡ls₁++x∷ls₂ hf₂)))
                ≡₂ : proj₁ (oracle x) (S.exec s (reverse b)) ≡ proj₁ (oracle x) (S.exec s ls₁)
                ≡₂ = S.h₄ (S.exec s (reverse b)) (S.exec s ls₁) x (all≡ s (S.Creads (S.exec s ls₁) x) (reverse b) ls₁ ls₂ dsj₁ ∀₂)
                all₁ : All (λ f₂ → S.exec s ls₁ f₂ ≡ run oracle x (S.exec s ls₁) f₂) (S.reads (run oracle x (S.exec s ls₁)) ls₂)
                all₁ = St.lemma5 {S.exec s ls₁} (S.reads (run oracle x (S.exec s ls₁)) ls₂) (proj₂ (proj₁ (oracle x) (S.exec s ls₁))) (hfr→disjoint s x (reverse b) ls₁ ls₂ hfr₁)


-}

↭-reverse : ∀ (xs : Build) → xs ↭ reverse xs
↭-reverse xs = subst (λ x → x ↭ reverse xs) (++-identityʳ xs) (++↭ʳ++ xs [])

reordered : ∀ {s} b₁ b₂ ls → b₁ ↭ b₂ → UniqueEvidence b₂ b₁ (map proj₁ ls) → HazardFree s b₁ [] ls → HazardFree s b₂ b₁ ls → (∀ f₁ → exec s b₁ f₁ ≡ exec s b₂ f₁)
reordered b₁ b₂ ls ↭₁ (ub₂ , ub₁ , uls , dsj) hf₁ hf₂ f₁ with reordered-inner (reverse b₁) b₂ ls {trans (length-reverse b₁) (↭-length ↭₁)} (↭-trans (↭-sym (↭-reverse b₁)) ↭₁) (ub₂ , (unique-reverse b₁ ub₁) , uls , dsj) (subst (λ x → HazardFree _ x [] ls) (sym (reverse-involutive b₁)) hf₁) (subst (λ x → HazardFree _ b₂ x ls) (sym (reverse-involutive b₁)) hf₂) f₁
... | ≡₁ = subst (λ x → exec _ x f₁ ≡ exec _ b₂ f₁) (reverse-involutive b₁) ≡₁

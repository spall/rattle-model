
open import Functional.State as St using (F ; System ; Cmd ; extend ; read ; Memory)

module Functional.Script.Proofs (oracle : F) where

open import Agda.Builtin.Equality
open import Functional.State.Helpers (oracle) using (cmdWriteNames ; run ; cmdReadNames ; cmdWrites)
open import Functional.State.Properties (oracle) using (lemma5)
open import Functional.Script.Exec (oracle) using (script ; buildWriteNames ; buildReadNames)
open import Functional.Script.Hazard (oracle) using (HazardFree ; FileInfo)
open import Functional.Script.Hazard.Properties (oracle) using (hf-∷ʳ-l ; hf-drop-mid ; hf=>disjoint ; hf=>disjointRW ; hf=>disjointWW ; hf=>disjointWR)
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
open import Data.List.Membership.Propositional using (_∈_ ; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-∃++ ; ∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any as Any using (here ; there)
open import Data.List.Relation.Unary.Any.Properties using (reverse⁺ ; reverse⁻)
open import Relation.Binary.PropositionalEquality using (subst ; subst₂ ; sym ; trans)
open import Data.List.Relation.Unary.All as All using (All ; _∷_ ; lookup)
open import Data.List.Relation.Unary.All.Properties as AllP hiding (++⁺)
open import Relation.Nullary using (¬_)
open import Functional.Build using (Build ; UniqueEvidence)
open import Functional.Script.Properties (oracle) using (exec-f₁≡ ; exec-≡f₁ ; writes≡)

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

unique=>∉ : ∀ (x : Cmd) xs → All (λ y → ¬ x ≡ y) xs → x ∉ xs
unique=>∉ x xs px x₁ with lookup px x₁
... | a = a refl

unique=>¬ : ∀ (v : Cmd) x xs ys → v ∈ ys → Unique (xs ++ x ∷ ys) → ¬ v ≡ x
unique=>¬ v x [] ys v∈ys (px ∷ u) = λ x₁ → (lookup px v∈ys) (sym x₁)
unique=>¬ v x (x₁ ∷ xs) ys v∈ys (px ∷ u) = unique=>¬ v x xs ys v∈ys u

unique-reverse : ∀ xs → Unique xs → Unique (reverse xs)
unique-reverse [] u = []
unique-reverse (x₁ ∷ xs) (px ∷ u) with ++⁺ (unique-reverse xs u) (All.[] ∷ []) (unique→disjoint (reverse xs) (all-reverse xs px))
... | u₁ = subst (λ ls → Unique ls) (sym (unfold-reverse x₁ xs)) u₁

{- length equivalence just makes the proof smaller -}
-- all of those unique and disjoint things are called UniqueEvidence now so replace to make it look better.
reordered-inner : ∀ {s} b₁ b₂ ls → {length b₁ ≡ length b₂} → b₁ ↭ b₂ → UniqueEvidence b₂ b₁ (map proj₁ ls) → HazardFree s (reverse b₁) [] ls → HazardFree s b₂ (reverse b₁) ls → (∀ f₁ → script s (reverse b₁) f₁ ≡ script s b₂ f₁)
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
... | ∀₁ = λ f₁ → subst₂ (λ x₁ x₂ → script s x₁ f₁ ≡ script s x₂ f₁)
                                            (sym (unfold-reverse x b₁)) (sym b₂≡xs++x∷ys)
                                            (exec-f₁≡ s f₁ x (reverse b₁) xs ys ∀₁ ≡₁ all₁ dsj₁)
          -- need to prove x does the same thing in both builds.
    where g₃ : x ∉ reverse b₁
          g₃ x∈rev = unique=>∉ x b₁ px (reverse⁻ x∈rev)
          g₁ : ∀ {v} → v ∈ ys → v ∈ reverse b₁
          g₁ v∈ys with ∈-resp-↭ (↭-sym ↭₁) (subst (λ x₁ → _ ∈ x₁) (sym b₂≡xs++x∷ys) (∈-++⁺ʳ xs (there v∈ys)))
          ... | v∈x∷b₁ with Any.tail (unique=>¬ _ x xs ys v∈ys (subst (λ x₁ → Unique x₁) b₂≡xs++x∷ys ub₂)) v∈x∷b₁
          ... | v∈b₁ = reverse⁺ v∈b₁
          dsj₁ : Disjoint (cmdWriteNames x (script s xs)) (buildWriteNames (run x (script s xs)) ys)
          dsj₁ = hf=>disjointWW s x xs ys (reverse b₁) ls (λ x₁ → g₁ x₁) g₃ (subst₂ (λ x₁ x₂ → HazardFree s x₁ x₂ ls) b₂≡xs++x∷ys (unfold-reverse x b₁) hf₂)
          dsj₃ : Disjoint (cmdReadNames x (script s xs)) (buildWriteNames (run x (script s xs)) ys)
          dsj₃ = hf=>disjointRW s x xs ys (reverse b₁) ls (λ x₁ → g₁ x₁) g₃ (subst₂ (λ x₁ x₂ → HazardFree s x₁ x₂ ls) b₂≡xs++x∷ys (unfold-reverse x b₁) hf₂)
          dsj₄ : Disjoint (cmdWriteNames x (script s xs)) (buildReadNames (run x (script s xs)) ys)
          dsj₄ = hf=>disjointWR s x xs ys (reverse b₁) ls (λ x₁ → g₁ x₁) g₃ (subst₂ (λ x₁ x₂ → HazardFree s x₁ x₂ ls) b₂≡xs++x∷ys (unfold-reverse x b₁) hf₂)
          dsj₂ : Disjoint (cmdReadNames x (script s xs)) (buildWriteNames (script s xs) ys)
          dsj₂ = subst (λ x₁ → Disjoint _ x₁) (sym (writes≡ (script s xs) (run x (script s xs)) ys (lemma5 (buildReadNames (run x (script s xs)) ys) (cmdWrites x (script s xs)) dsj₄)))
                       dsj₃
          ≡₁ : proj₁ (oracle x) (script s (reverse b₁)) ≡ proj₁ (oracle x) (script s xs)
          ≡₁ = sym (proj₂ (oracle x) (script s xs) (script s (reverse b₁))
               λ f₁ x₁ → trans (exec-≡f₁ s f₁ xs ys λ x₂ → dsj₂ (x₁ , x₂)) (sym (∀₁ f₁)))
          all₁ : All (λ f₁ → script s xs f₁ ≡ run x (script s xs) f₁) (buildReadNames (run x (script s xs)) ys)
          all₁ = lemma5 (buildReadNames (run x (script s xs)) ys) (cmdWrites x (script s xs))
                 (hf=>disjoint s x xs ys (reverse b₁) ls (λ x₁ → g₁ x₁) g₃ (subst₂ (λ x₁ x₂ → HazardFree s x₁ x₂ ls) b₂≡xs++x∷ys (unfold-reverse x b₁) hf₂))

↭-reverse : ∀ (xs : Build) → xs ↭ reverse xs
↭-reverse xs = subst (λ x → x ↭ reverse xs) (++-identityʳ xs) (++↭ʳ++ xs [])

reordered : ∀ {s} b₁ b₂ ls → b₁ ↭ b₂ → UniqueEvidence b₂ b₁ (map proj₁ ls) → HazardFree s b₁ [] ls → HazardFree s b₂ b₁ ls → (∀ f₁ → script s b₁ f₁ ≡ script s b₂ f₁)
reordered b₁ b₂ ls ↭₁ (ub₂ , ub₁ , uls , dsj) hf₁ hf₂ f₁ with reordered-inner (reverse b₁) b₂ ls {trans (length-reverse b₁) (↭-length ↭₁)} (↭-trans (↭-sym (↭-reverse b₁)) ↭₁) (ub₂ , (unique-reverse b₁ ub₁) , uls , dsj) (subst (λ x → HazardFree _ x [] ls) (sym (reverse-involutive b₁)) hf₁) (subst (λ x → HazardFree _ b₂ x ls) (sym (reverse-involutive b₁)) hf₂) f₁
... | ≡₁ = subst (λ x → script _ x f₁ ≡ script _ b₂ f₁) (reverse-involutive b₁) ≡₁

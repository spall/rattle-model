module Functional.Build where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat using (suc ; zero) renaming (Nat to ℕ)
open import Data.Nat using (_<_ ; _>_)
open import Data.List using (List ; [] ; _∷_ ; reverse)
open import Functional.State using (Cmd)
open import Data.Product using (_×_ ; _,_ ; Σ-syntax ; proj₁ ; proj₂)
open import Data.Product.Properties using (,-injectiveˡ ; ,-injectiveʳ)

open import Data.Bool using (if_then_else_)
open import Data.String using (_==_)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.List.Relation.Unary.AllPairs using (AllPairs ; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Data.Nat.Properties as N using (1+n≢n ; 1+n≰n ; ≤-refl ; ≤-step)
open import Relation.Binary.PropositionalEquality using (subst ; cong ; sym ; trans)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup)

Build : Set
Build = List Cmd

-- Proof the pairs are not equal. 
_¬≡-⊎->_ : (Cmd × ℕ) → (Cmd × ℕ) → Set
(x , n₁) ¬≡-⊎-> (y , n₂) = ¬ x ≡ y ⊎ n₁ > n₂

-- get the evidence we need that the values are not equal.
¬≡-⊎->⇒¬≡ : ∀ x x₁ ls → All (x ¬≡-⊎->_) ls → x₁ ∈ ls → ¬ x ≡ x₁
¬≡-⊎->⇒¬≡ x x₁ ls all x₁∈ls with lookup all x₁∈ls
... | inj₁ ¬x≡x₁ = λ x≡x₁ → ¬x≡x₁ (,-injectiveˡ x≡x₁)
... | inj₂ x>x₁ = λ x≡x₁ → 1+n≰n (subst (λ x₂ → _ > x₂) (sym (,-injectiveʳ x≡x₁)) x>x₁)

Unique-> : List (Cmd × ℕ) → Set
Unique-> ls = AllPairs _¬≡-⊎->_ ls

NBuild : Set
NBuild = List (Cmd × ℕ)

-- NBuild is meant to be reverse now because it was easier to construct unique evidence
ΣNBuild : Set
ΣNBuild = Σ[ ls ∈ NBuild ](Unique-> ls)

All⇒All : ∀ x n → (ls : List (Cmd × ℕ)) → All (_¬≡-⊎->_ (x , n)) ls → All (_¬≡-⊎->_ (x , suc n)) ls
All⇒All x n [] All.[] = All.[]
All⇒All x n (x₂ ∷ ls) (px All.∷ all) with x ≟ proj₁ x₂
... | no ¬x≡x₂ = inj₁ ¬x≡x₂ All.∷ All⇒All x n ls all 
... | yes x≡x₂ with px
... | inj₁ ¬x≡x₂ = contradiction x≡x₂ ¬x≡x₂
... | inj₂ n>sx₂ = inj₂ (≤-step n>sx₂) All.∷ All⇒All x n ls all

{- Gives us a new N and proof that the new pair will be unique -}
getN : (x : Cmd) → (ls : NBuild) → Unique-> ls → Σ[ n ∈ ℕ ](All (_¬≡-⊎->_ (x , n)) ls)
getN x [] AllPairs.[] = zero , All.[]
getN x (x₁ ∷ ls) (px ∷ p) with x ≟ proj₁ x₁
... | yes x≡x₁ = suc (proj₂ x₁) , inj₂ (Data.Nat.s≤s ≤-refl) All.∷ subst (λ x₂ → All (_¬≡-⊎->_ (x₂ , suc (proj₂ x₁))) ls)
                                                                                 (sym x≡x₁)
                                                                                 (All⇒All (proj₁ x₁) (proj₂ x₁) ls px)
... | no ¬x≡x₁ with getN x ls p
... | n , p₁ = n , inj₁ ¬x≡x₁ All.∷ p₁

-- reverses the build and numbers it. 
number : Build → ΣNBuild
number b = g₁ (reverse b)
  where g₁ : Build → Σ[ ls ∈ NBuild ](Unique-> ls)
        g₁ [] = ([] , AllPairs.[])
        g₁ (x ∷ b) with g₁ b
        ... | ls , u with getN x ls u
        ... | n , p = (x , n) ∷ ls , p AllPairs.∷ u

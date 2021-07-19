
open import Functional.State using (F ; run-≡ ; run)

module Functional.Script.Hazard.Properties (oracle : F) where

open import Common.List.Properties using (_before_en_)
open import Agda.Builtin.Equality
open import Functional.Script.Hazard.Base (oracle) using (HazardFree ; [] ; :: ; cmdReads ; cmdWrites ; files ; cmdsRun ; cmdWrote ; cmdWrote-⊆ ; files-⊆)
open import Data.List as L using (_∷_ ; _++_ ; map)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (subst ; subst₂ ; cong ; sym)
open import Function using (_∘_)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Data.String using (String)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List.Properties using (map-++-commute)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (Any-resp-⊆ ; ++⁺ ; ⊆-refl ; xs⊆ys++xs)

hf-≡ : ∀ as {bs} {cs} s₂ s₁ {b₁} {b₂} → (∀ f₁ → s₂ f₁ ≡ s₁ f₁) → HazardFree s₂ b₁ b₂ (as ++ bs ++ cs) → HazardFree s₁ b₁ b₂ (as ++ cs)
hf-≡ as s₂ s₁ ∀₁ [] = ?
hf-≡ as s₂ s₁ ∀₁ (:: .s₂ .(as ++ _ ++ _) x b₁ _ x₁ x₂ hf) = ?

{-
hf-≡ as s₂ s₁ ∀₁ [] = []
hf-≡ as {bs} {cs} s₂ s₁ ∀₁ (:: .s₂ ls x b₁ b₂ ¬sh dsj hf) with hf-≡ ((x , cmdReads s₂ x , cmdWrites s₂ x) ∷ as) {bs} {cs} (run oracle x s₂) (run oracle x s₁) (run-≡ {oracle} x ∀₁) hf
... | hf₁ with subst₂ (λ x₃ x₄ → HazardFree _ b₁ b₂ ((x , x₃ , x₄) ∷ as ++ cs)) ≡reads ≡writes hf₁
  where ≡₁ : proj₁ (oracle x) s₂ ≡ proj₁ (oracle x) s₁
        ≡₁ = proj₂ (oracle x) s₂ s₁ λ f₁ x₃ → ∀₁ f₁
        ≡reads : cmdReads s₂ x ≡ cmdReads s₁ x
        ≡reads = cong ((map proj₁) ∘ proj₁) ≡₁
        ≡writes : cmdWrites s₂ x ≡ cmdWrites s₁ x
        ≡writes = cong ((map proj₁) ∘ proj₂) ≡₁
... | hf₂ = :: s₁ (as ++ cs) x b₁ b₂ ¬sh₁ dsj₁ hf₂
  where ≡₁ : proj₁ (oracle x) s₂ ≡ proj₁ (oracle x) s₁
        ≡₁ = proj₂ (oracle x) s₂ s₁ λ f₁ x₃ → ∀₁ f₁
        ≡writes : cmdWrites s₂ x ≡ cmdWrites s₁ x
        ≡writes = cong ((map proj₁) ∘ proj₂) ≡₁
        
        dsj₁ : Disjoint (cmdWrites s₁ x) (files (as ++ cs))
        dsj₁ = λ x₂ → dsj (subst (λ x₃ → _ ∈ x₃) (sym ≡writes) (proj₁ x₂) , files-⊆ {as ++ cs} (++⁺ ⊆-refl (xs⊆ys++xs cs bs)) (proj₂ x₂))
        ≡reads : cmdReads s₂ x ≡ cmdReads s₁ x
        ≡reads = cong ((map proj₁) ∘ proj₁) ≡₁
        v∈₁ : ∀ {x₁} {v} → v ∈ cmdWrote (as ++ cs) x₁ → v ∈ cmdWrote (as ++ bs ++ cs) x₁
        v∈₁ {x₁} v∈ = cmdWrote-⊆ x₁ {as ++ cs} (++⁺ ⊆-refl (xs⊆ys++xs cs bs)) v∈
        ¬sh₁ : ∀ x₁ → x before x₁ en b₂ → Disjoint (cmdReads s₁ x) (cmdWrote (as ++ cs) x₁)
        ¬sh₁ = λ x₁ x₃ x₄ → ¬sh x₁ x₃ (subst (λ x₂ → _ ∈ x₂) (sym ≡reads) (proj₁ x₄) , v∈₁ (proj₂ x₄))
-}

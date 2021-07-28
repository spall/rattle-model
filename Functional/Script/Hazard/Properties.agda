{-# OPTIONS --allow-unsolved-metas #-}
open import Functional.State using (F ; run-≡ ; run ; System ; Cmd)

module Functional.Script.Hazard.Properties (oracle : F) where

open import Functional.Script.Exec (oracle) using (exec)
open import Functional.Build using (Unique-> ; Build)
open import Common.List.Properties using (_before_en_)
open import Agda.Builtin.Equality
open import Functional.File using (FileName)
open import Functional.Script.Hazard.Base (oracle) using (HazardFree ; [] ; :: ; cmdReads ; cmdWrites ; files ; cmdsRun ; cmdWrote ; FileInfo ; ΣFileInfo ; save ; filesRead ; ¬SpeculativeHazard)
open import Data.List as L using (_∷_ ; _++_ ; map ; foldr ; List ; foldl ; _∷ʳ_)
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; _×_ ; Σ-syntax ; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (subst ; subst₂ ; cong ; sym ; trans)
open import Function using (_∘_)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Data.String using (String)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List.Properties using (map-++-commute)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (Any-resp-⊆ ; ++⁺ ; ⊆-refl ; xs⊆ys++xs)
open import Data.List.Relation.Unary.AllPairs using (AllPairs ; _∷_)

{- what does memoize do about duplicates? 

  The following property is nice: build is idempotent

    
  
  #1 write #2 

  #2 write ()

  we shouldn't care about forward builds with duplicate commands; because builds can't be idempotent 

-}
save1 : Cmd → System → ΣFileInfo → ΣFileInfo
save1 x s = save x (cmdReads s x) (cmdWrites s x)

save-foldr : (ΣFileInfo × System) → Build → (ΣFileInfo × System)
save-foldr = foldr (λ x₁ (zs , s₁) → save1 x₁ s₁ zs , run oracle x₁ s₁)

filesPair : ΣFileInfo → List (List FileName × List FileName)
filesPair = map proj₂ ∘ proj₁

lemma1 : ∀ {s₁} {s₂} {s} {x} {xs} {ys} x₀ → (∀ f₁ → s₂ f₁ ≡ s₁ f₁) → files (proj₁ (save-foldr (xs , s) ys)) ⊆ files (proj₁ (save-foldr (save1 x s xs , run oracle x s) ys)) → Disjoint (cmdWrites s₁ x₀) (files (proj₁ (save-foldr (save1 x s xs , run oracle x s) ys))) → Disjoint (cmdWrites s₂ x₀) (files (proj₁ (save-foldr (xs , s) ys)))
lemma1 {s₁} {s₂} x₀ ∀₁ ⊆₁ dsj = λ x₁ → dsj (v∈writes (proj₁ x₁) , ⊆₁ (proj₂ x₁))
  where ≡₁ : proj₁ (oracle x₀) s₂ ≡ proj₁ (oracle x₀) s₁
        ≡₁ = proj₂ (oracle x₀) s₂ s₁ λ f₁ _ → ∀₁ f₁
        v∈writes : ∀ {v} → v ∈ cmdWrites s₂ x₀ → v ∈ cmdWrites s₁ x₀
        v∈writes = subst (λ x₁ → _ ∈ x₁) (cong (map proj₁ ∘ proj₂) ≡₁)

lemma2 : ∀ {xs} {s} {ys} {x} {x₀} → (∀ f₁ → proj₂ (save-foldr (xs , s) ys) f₁ ≡ proj₂ (save-foldr (save1 x s xs , run oracle x s) ys) f₁) → files (proj₁ (save-foldr (xs , s) ys)) ⊆ files (proj₁ (save-foldr (save1 x s xs , run oracle x s) ys))→ files (proj₁ (save-foldr (xs , s) (x₀ ∷ ys))) ⊆ files (proj₁ (save-foldr (save1 x s xs , run oracle x s) (x₀ ∷ ys)))
lemma2 {xs} {s} {ys} {x} {x₀} ∀₁ ⊆₁ x₂ with ∈-++⁻ (filesRead (proj₁ (save-foldr (xs , s) (x₀ ∷ ys)))) x₂
{- v ∈ reads -}
... | inj₁ ∈₁ with ∈-++⁻ (cmdReads (proj₂ p) x₀) ∈₁
  where p : (ΣFileInfo × System)
        p = save-foldr (xs , s) ys
{- in cmdreads of x₀ -}
... | inj₁ ∈₂ =  ∈-++⁺ˡ (∈-++⁺ˡ (subst (λ x₃ → _ ∈ x₃) ≡₁ ∈₂))
  where ≡₁ : cmdReads (proj₂ (save-foldr (xs , s) ys)) x₀ ≡ cmdReads (proj₂ (save-foldr (save1 x s xs , run oracle x s) ys)) x₀
        ≡₁ = cong (map proj₁ ∘ proj₁) (proj₂ (oracle x₀) (proj₂ (save-foldr (xs , s) ys)) (proj₂ (save-foldr (save1 x s xs , run oracle x s) ys)) λ f₁ x₁ → ∀₁ f₁)
        
{- we know v ∈ cmdReads (proj₂ (save-foldr (xs , s) ys)) x₀
   we want to know v∈ cmdReads (proj₂ (save-foldr (save1 x s xs , run oracle x s) ys)) x₀
-}

... | inj₂ ∈₂ with ∈-++⁻ (filesRead (proj₁ (save-foldr (save1 x s xs , run oracle x s) ys))) (⊆₁ (∈-++⁺ˡ ∈₂))
{- v ∈ reads-}
... | inj₁ ∈₃ = ∈-++⁺ˡ (∈-++⁺ʳ (cmdReads (proj₂ (save-foldr (save1 x s xs , run oracle x s) ys)) x₀) ∈₃)
{- v ∈ writes -}
... | inj₂ ∈₃ = ∈-++⁺ʳ (filesRead (proj₁ (save-foldr (save1 x s xs , run oracle x s) (x₀ ∷ ys)))) (∈-++⁺ʳ (cmdWrites (proj₂ (save-foldr (save1 x s xs , run oracle x s) ys)) x₀) ∈₃)

{- v ∈ writes -}
lemma2 {xs} {s} {ys} {x} {x₀} ∀₁ ⊆₁ x₂ | inj₂ ∈₁ with ∈-++⁻ (cmdWrites (proj₂ (save-foldr (xs , s) ys)) x₀) ∈₁
... | inj₁ ∈₂ = ∈-++⁺ʳ (filesRead (proj₁ (save-foldr (save1 x s xs , run oracle x s) (x₀ ∷ ys)))) (∈-++⁺ˡ (subst (λ x₃ → _ ∈ x₃) ≡₁ ∈₂))
  where ≡₁ : cmdWrites (proj₂ (save-foldr (xs , s) ys)) x₀ ≡ cmdWrites (proj₂ (save-foldr (save1 x s xs , run oracle x s) ys)) x₀
        ≡₁ = cong (map proj₁ ∘ proj₂) (proj₂ (oracle x₀) (proj₂ (save-foldr (xs , s) ys)) (proj₂ (save-foldr (save1 x s xs , run oracle x s) ys)) λ f₁ x₁ → ∀₁ f₁)
... | inj₂ ∈₂ with ∈-++⁻ (filesRead (proj₁ (save-foldr (save1 x s xs , run oracle x s) ys))) (⊆₁ (∈-++⁺ʳ (filesRead (proj₁ (save-foldr (xs , s) ys))) ∈₂))
{- v ∈ reads-}
... | inj₁ ∈₃ = ∈-++⁺ˡ (∈-++⁺ʳ (cmdReads (proj₂ (save-foldr (save1 x s xs , run oracle x s) ys)) x₀) ∈₃)
{- v ∈ writes -}
... | inj₂ ∈₃ = ∈-++⁺ʳ (filesRead (proj₁ (save-foldr (save1 x s xs , run oracle x s) (x₀ ∷ ys)))) (∈-++⁺ʳ (cmdWrites (proj₂ (save-foldr (save1 x s xs , run oracle x s) ys)) x₀) ∈₃)

-- s₁ = (proj₂ (save-foldr (xs , s) ys))
-- s₂ = (proj₂ (save-foldr (save1 x s xs , run oracle x s) ys))

{- 1. increment the number of x₁ or x₂ depending on where x got placed and what its value is.
   2. show these new values have the same order in the new fileinfo with x
   3. we need to know x₂ (the reader) is in b, so if we increment its value how can we know its still in b?
     We know x is going to have run and changed nothing in the system. 
-}

lemma3 : ∀ {b₂} {x₀} {s₁} {s₂} {xs} {ys} {s} {x} → ¬SpeculativeHazard b₂ (save x₀ (cmdReads s₂ x₀) (cmdWrites s₂ x₀) (proj₁ (save-foldr (save1 x s xs , run oracle x s) ys))) → ¬SpeculativeHazard b₂ (save x₀ (cmdReads s₁ x₀) (cmdWrites s₁ x₀) (proj₁ (save-foldr (xs , s) ys)))
lemma3 ¬sh x₁ x₂ x x₃ x₄ x₅ = ¬sh x₁ x₂ {!!} x₃ x₄ {!!}

{- the negation has given us evidence there is a hazard in the build where we DID NOT run x; so we need to show that if we add x in
   there is still a hazard.  so it depends on where x goes? because adding a command can change the tuple values of the other commands
after it in the build.  the same hazard exists, but we need to increment the number associated with the command? -}


{- We know in the build where we run x, there are no hazards, so we have evidence -}

hf-≡ : ∀ {xs} {x} {b₂} s (ys : Build) (b₁ : Build) → files (proj₁ (save-foldr (xs , s) ys)) ⊆ files (proj₁ (save-foldr (save1 x s xs , run oracle x s) ys)) → (∀ f₁ → (proj₂ (save-foldr (xs , s) ys)) f₁ ≡ (proj₂ (save-foldr (save1 x s xs , run oracle x s) ys)) f₁) → HazardFree (proj₂ (save-foldr (save1 x s xs , run oracle x s) ys)) b₁ b₂ (proj₁ (save-foldr (save1 x s xs , run oracle x s) ys)) → HazardFree (proj₂ (save-foldr (xs , s) ys)) b₁ b₂ (proj₁ (save-foldr (xs , s) ys))
hf-≡ s ys L.[] ⊆₁ ∀₁ HazardFree.[] = HazardFree.[]
hf-≡ {xs} {x} s ys (x₀ ∷ b₁) ⊆₁ ∀₁ (HazardFree.:: _ _ x₀ b₁ b₂ ¬sh dsj hf) with hf-≡ s (x₀ ∷ ys) b₁ (lemma2 {xs} {s} {ys} {x} {x₀} ∀₁ ⊆₁) (run-≡ {oracle} x₀ ∀₁) hf
... | hf₁ = HazardFree.:: (proj₂ (save-foldr (xs , s) ys)) (proj₁ (save-foldr (xs , s) ys)) x₀ b₁ b₂ (lemma3 ¬sh) (lemma1 {(proj₂ (save-foldr (save1 x s xs , run oracle x s) ys))} {(proj₂ (save-foldr (xs , s) ys))} {s} {x} {xs} {ys} x₀ ∀₁ ⊆₁ dsj) hf₁

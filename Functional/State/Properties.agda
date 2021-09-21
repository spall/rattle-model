
open import Functional.State using (Oracle ; System ; extend ; Cmd) 

module Functional.State.Properties (oracle : Oracle) where

open import Agda.Builtin.Equality
open import Functional.File using (Files ; FileName ; FileNames)
open import Functional.State.Helpers (oracle) using (cmdFiles ; run ; cmdWriteNames ; cmdReadNames ; cmdWrites ; getNames)
open import Data.List using (map ; foldr ; [] ; _∷_)
open import Data.String using (_≟_)
open import Data.String.Properties using (≡-decSetoid)
open import Data.List.Membership.Propositional using (_∈_ ; _∉_)
open import Data.List.Membership.DecSetoid (≡-decSetoid) using (_∈?_)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Data.Product using (proj₁ ; proj₂ ; _,_)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Relation.Binary.PropositionalEquality using (trans ; subst)

-- proofs that used to be in the State.agda file

{- if f₁ is in ls, then f₁ will be the same after both systems are extended with ls -}
lemma4 : {s s₁ : System} (ls : Files) -> (f₁ : FileName) -> f₁ ∈ getNames ls -> foldr extend s ls f₁ ≡ foldr extend s₁ ls f₁
lemma4 ((f₂ , v₂) ∷ ls) f₁ f₁∈writes with f₂ ≟ f₁
... | yes f₂≡f₁ = refl
... | no ¬f₂≡f₁ = lemma4 ls f₁ (tail (λ f₁≡f₂ → ¬f₂≡f₁ (sym f₁≡f₂)) f₁∈writes)


{- if f₁ is not in ls then value of f₁ will be the same as in the original system after the system
   is extended with ls -}
lemma3 : ∀ {s} f₁ ls → f₁ ∉ getNames ls → s f₁ ≡ foldr extend s ls f₁
lemma3 f₁ [] f₁∉ = refl
lemma3 f₁ ((f₂ , v₂) ∷ ls) f₁∉ with f₂ ≟ f₁
... | yes f₂≡f₁ = contradiction (here (sym f₂≡f₁)) f₁∉
... | no ¬f₂≡f₂ = lemma3 f₁ ls (λ x → f₁∉ (there x))


{- if results of x are the same when run in 2 systems, and f₁ is the same in both systems, 
   then f₁ is the same in the new systems after running x in both systems
-}
lemma2 : ∀ {s₁} {s₂} {f₁} {x} → cmdFiles x s₁ ≡ cmdFiles x s₂ -> s₁ f₁ ≡ s₂ f₁ -> run x s₁ f₁ ≡ run x s₂ f₁
lemma2 {s} {s₁} {f₁} {x} result≡ ≡₁ with f₁ ∈? cmdWriteNames x s
... | yes f₁∈ws
  = subst (λ x₁ → foldr extend s (cmdWrites x s) f₁ ≡ foldr extend s₁ (proj₂ x₁) f₁)
          result≡
          (lemma4 {s} {s₁} (cmdWrites x s) f₁ f₁∈ws)
... | no f₁∉ws
  = trans (sym (lemma3 f₁ (cmdWrites x s) f₁∉ws))
          (trans ≡₁ (lemma3 f₁ (cmdWrites x s₁) (subst (λ p → f₁ ∉ getNames (proj₂ p)) result≡ f₁∉ws)))


{- if x's inputs are the same in both systems then everything in ls will still be
   the same in the new systems after running x in both -}
lemma1 : ∀ {s} {s₁} ls x → All (λ f₁ → s f₁ ≡ s₁ f₁) (cmdReadNames x s) -> All (λ f₁ → s f₁ ≡ s₁ f₁) ls -> All (λ f₁ → run x s f₁ ≡ run x s₁ f₁) ls
lemma1 [] x all₁ all₂ = All.[]
lemma1 {s} {s₁} (f₁ ∷ ls) x all₁ (px All.∷ all₂) with proj₂ (oracle x) s s₁ (λ f₁ x₂ → lookup all₁ x₂)
... | result≡ = (lemma2 {s} {s₁} result≡ px) All.∷ (lemma1 {s} {s₁} ls x all₁ all₂)

lemma1-sym : {s s₁ : System} (ls : FileNames) -> (x : Cmd) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (cmdReadNames x s₁) -> All (λ f₁ → s f₁ ≡ s₁ f₁) ls -> All (λ f₁ → run x s f₁ ≡ run x s₁ f₁) ls
lemma1-sym [] x all₁ all₂ = All.[]
lemma1-sym {s} {s₁} (x₁ ∷ ls) x all₁ (px All.∷ all₂) with proj₂ (oracle x) s₁ s (λ f₁ x₂ → sym (lookup all₁ x₂))
... | result≡ = (lemma2 {s} {s₁} (sym result≡) px) All.∷ (lemma1-sym {s} {s₁} ls x all₁ all₂)


lemma5 : {s : System} (ls : FileNames) (ls₁ : Files) -> Disjoint (getNames ls₁) ls -> All (λ f₁ → s f₁ ≡ foldr extend s ls₁ f₁) ls
lemma5 [] ls₁ dsj = All.[]
lemma5 (x ∷ ls) ls₁ dsj with x ∈? getNames ls₁
... | yes x∈ = contradiction (x∈ , here refl) dsj
... | no x∉ = (lemma3 x ls₁ x∉) All.∷ (lemma5 ls ls₁ λ x₁ → dsj (proj₁ x₁ , there (proj₂ x₁)))

run-≡ : {sys sys₁ : System} (x : Cmd) -> (∀ f₁ → sys f₁ ≡ sys₁ f₁) -> (∀ f₁ → run x sys f₁ ≡ run x sys₁ f₁)
run-≡ {sys} {sys₁} x ∀₁ f₁ = lemma2 {sys} {sys₁} ≡₁ (∀₁ f₁)
  where ≡₁ : cmdFiles x sys ≡ cmdFiles x sys₁
        ≡₁ = proj₂ (oracle x) sys sys₁ λ f₂ x₁ → ∀₁ f₂
  

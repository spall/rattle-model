
module Functional.Proofs where

open import Agda.Builtin.Equality

open import Data.List using ([] ; List ; _++_ ; _∷_ ; map ; foldr)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; ∃-syntax)
open import Functional.State using (F ; System ; empty ; trace ; Cmd ; run ; extend)
open import Functional.Build using (Build)
open import Functional.Script.Exec as S using (HazardFree ; writes ; Cons)
open import Functional.Forward.Exec as Forward hiding (run)
open import Functional.File using (FileName ; Files)
open import Functional.Rattle.Exec as Rattle hiding (run)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_ ; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭)
open import Data.String.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (trans ; sym ; decSetoid ; setoid ; cong₂ ; cong)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Relation.Nullary using (yes ; no)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-trans)
open import Data.List.Relation.Unary.Any using (there ; here)
open import Data.List.Relation.Unary.Any.Properties using (++⁻)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Relation.Nullary.Negation using (contradiction)


{- if cmd does not write to file given sys; then value of file in sys is same before and after cmd runs -}
lemma10 : {f : F} {sys : System} (cmd : Cmd) -> (f₁ : FileName) -> f₁ ∉ proj₂ (trace f sys cmd) -> sys f₁ ≡ run f cmd sys f₁
lemma10 {f} {sys} cmd f₁ p = g (proj₂ (proj₁ (f cmd) sys)) p
  where g : (ls : Files) -> f₁ ∉ map proj₁ ls -> sys f₁ ≡ foldr extend sys ls f₁
        g [] p = refl
        g ((f₂ , v₂) ∷ ls) p with f₂ ≟ f₁
        ... | yes f₂≡f₁ = contradiction (here (sym f₂≡f₁)) p
        ... | no ¬f₂≡f₁ = g ls λ x → p (there x)
        

{- if build does not write to file given sys; then value of file in sys is same before and after build runs -}
lemma9 : {f : F} {sys : System} (f₁ : FileName) -> (b : Build) -> f₁ ∉ writes f sys b -> S.exec f sys b f₁ ≡ sys f₁
lemma9 f₁ [] p = refl
lemma9 {f} {sys} f₁ (x ∷ b) p with lemma9 {f} {run f x sys} f₁ b (λ x₁ → p (∈-++⁺ʳ (proj₂ (trace f sys x)) x₁)) | lemma10 {f} {sys} x f₁ λ x₁ → p (∈-++⁺ˡ x₁)
... | a | a₁ = trans a (sym a₁)


lemma8 : {ls ls₁ ls₂ : List FileName} -> ls₁ ⊆ ls -> ls₂ ⊆ ls -> ls₁ ++ ls₂ ⊆ ls
lemma8 ls₁⊆ls ls₂⊆ls = λ x₁ → f ls₁⊆ls ls₂⊆ls x₁
  where f : {ws xs ys : List FileName} {x₁ : FileName} -> ws ⊆ xs -> ys ⊆ xs -> x₁ ∈ ws ++ ys -> x₁ ∈ xs
        f {ws} ws⊆xs ys⊆xs x₁∈ws++ys with ++⁻ ws x₁∈ws++ys
        ... | inj₁ x = ws⊆xs x
        ... | inj₂ y = ys⊆xs y

{- prove the writes of the cmd x are in writes of b 
   basically try to do this by showing the inputs to x are the same; so x writes to the same files as the x in b -}
lemma7 : {f : F} {sys sys₁ : System} -> (x : Cmd) -> (b : Build) -> x ∈ b -> proj₂ (trace f sys₁ x) ⊆ writes f sys b
lemma7 {f} {sys} {sys₁} x b x∈b with f x
... | sys₂ , p = {!!} 

lemma6 : {f : F} {sys sys₁ : System} {ls : List FileName} (b b₂ : Build) -> HazardFree f sys b [] -> HazardFree f sys₁ b₂ ls -> b₂ ⊆ b -> writes f sys₁ b₂ ⊆ writes f sys b
lemma6 b [] hf hf₂ b₂⊆b = λ ()
lemma6 {f} {sys} {sys₁} b (x ∷ b₂) hf (Cons .x .b₂ _ x₁ hf₂) x∷b₂⊆b with lemma6 {f} {sys} {run f x sys₁} b b₂ hf hf₂ (⊆-trans (λ x₂ → there x₂) x∷b₂⊆b) | lemma7 {f} {sys} {sys₁} x b (x∷b₂⊆b (here refl))
... | writes-b₂⊆writes-b | writes-x⊆writes-b = lemma8 writes-x⊆writes-b writes-b₂⊆writes-b


lemma5 : {f : F} {sys : System} (b b₁ : Build) -> b₁ ⊆ b -> HazardFree f sys b [] -> HazardFree f sys b₁ [] -> (f₁ : FileName) -> f₁ ∉ writes f sys b -> f₁ ∉ writes f sys b₁
lemma5 {f} {sys} b b₁ b₁⊆b hf hf₁ f₁ f₁∉writes-b with lemma6 b b₁ hf hf₁ b₁⊆b
... | writes-b₁⊆writes-b = λ x → f₁∉writes-b (writes-b₁⊆writes-b x)


lemma4 : {f : F} {sys : System} (b b₁ : Build) -> b ⊆ b₁ -> HazardFree f sys b [] -> HazardFree f sys b₁ [] -> (f₁ : FileName) -> f₁ ∈ writes f sys b -> f₁ ∈ writes f sys b₁
lemma4 {f} {sys} b b₁ b⊆b₁ hf hf₁ f₁ f₁∈writes-b with lemma6 b₁ b hf₁ hf b⊆b₁
... | writes-b⊆writes-b₁ = writes-b⊆writes-b₁ f₁∈writes-b


lemma1 : {f : F} {sys : System} (b : Build) -> HazardFree f sys b [] -> ∀ f₁ → S.exec f sys b f₁ ≡ proj₁ (Forward.exec f (sys , empty) b) f₁
lemma1 b p = {!!}

script-reordered : {f : F} {sys : System} (b : Build) -> (b₂ : Build) -> b ↭ b₂ -> HazardFree f sys b [] -> HazardFree f sys b₂ [] -> ∀ f₁ → S.exec f sys b f₁ ≡ S.exec f sys b₂ f₁
script-reordered {f} {sys} b b₂ b↭b₂ hf hf₂ = λ f₁ → g f₁
  where g : (f₁ : FileName) -> S.exec f sys b f₁ ≡ S.exec f sys b₂ f₁
        g f₁ with f₁ ∈? writes f sys b
        ... | no ¬p = trans (lemma9 {f} {sys} f₁ b ¬p) (sym (lemma9 {f} {sys} f₁ b₂ (lemma5 b b₂ (λ x → ∈-resp-↭ (↭-sym b↭b₂) x) hf hf₂ f₁ ¬p)))
        ... | yes p = {!!}


forward-reordered : {f : F} {sys : System} (b : Build) -> (b₂ : Build) -> b ↭ b₂ -> HazardFree f sys b [] -> HazardFree f sys b₂ [] -> ∀ f₁ → proj₁ (Forward.exec f (sys , empty) b) f₁ ≡ proj₁ (Forward.exec f (sys , empty) b₂) f₁
forward-reordered {oc} {sys} b b₂ p p₂ p₃ = λ f₁ → f {oc} {sys} f₁ b b₂ p p₂ p₃
  where f : {f : F} {sys : System} (f₁ : FileName) -> (b : Build) -> (b₂ : Build) -> b ↭ b₂ -> HazardFree f sys b [] -> HazardFree f sys b₂ [] -> proj₁ (Forward.exec f (sys , empty) b) f₁ ≡ proj₁ (Forward.exec f (sys , empty) b₂) f₁
        f {oc} {sys} f₁ b b₂ p p₂ p₃ with script-reordered {oc} {sys} b b₂ p p₂ p₃ f₁ | lemma1 {oc} {sys} b p₂ f₁ | lemma1 {oc} {sys} b₂ p₃ f₁
        ... | a | a₂ | a₃ = trans (sym a₂) (trans a a₃)
        

rattle-reordered : {f : F} {sys : System} (b : Build) -> (b₂ : Build) -> b ↭ b₂ -> HazardFree f sys b [] -> HazardFree f sys b₂ [] -> ∀ f₁ → proj₁ (Rattle.exec f (sys , empty) b) f₁ ≡ proj₁ (Rattle.exec f (sys , empty) b₂) f₁
rattle-reordered b b₂ p p₂ p₃ = λ f₁ → f f₁
  where f : {f : F} {sys : System} (f₁ : FileName) -> proj₁ (Rattle.exec f (sys , empty) b) f₁ ≡ proj₁ (Rattle.exec f (sys , empty) b₂) f₁
        f {oc} {sys} f₁ = {!!}

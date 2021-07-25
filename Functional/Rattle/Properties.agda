{-# OPTIONS --allow-unsolved-metas #-}
open import Functional.State as St using (F ; System ; Memory ; Cmd ; trace ; extend ; State)

module Functional.Rattle.Properties (oracle : F) where

open import Agda.Builtin.Equality

open import Common.List.Properties using (∈-resp-≡ ; l11)
open import Functional.Forward.Properties (oracle) using (cmdReadWrites ; IdempotentState ; IdempotentCmd ; cmdIdempotent)
open import Functional.Forward.Exec (oracle) using (get ; maybeAll ; run?)
open import Functional.File using (FileName ; FileContent)
open import Data.Bool using (true ; false ; if_then_else_)

open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∃-syntax)
open import Data.Product.Properties using (,-injectiveʳ ; ,-injectiveˡ)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Data.List using (List ; map ; _++_ ; foldr ; _∷_ ; [] ; concatMap ; reverse ; _∷ʳ_)
open import Data.List.Properties using (∷-injective ; unfold-reverse)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Relation.Binary.PropositionalEquality using (trans ; cong ; cong-app ; sym ; decSetoid ; cong₂ ; subst ; inspect ; [_])
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-++⁻ ; ∈-concat⁻)
open import Function.Base using (_∘_)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Unary.Any using (tail)
open import Functional.Rattle.Exec (oracle) using (execWError ; runWError ; run ; doRun ; exec ; doRunWError ; checkHazard)
open import Functional.Build using (Build)
open import Data.Sum using (inj₂ ; from-inj₂ ; inj₁ )
open import Data.Sum.Properties using (inj₂-injective)
open import Functional.Script.Exec (oracle) as Script hiding (exec)
open import Functional.Script.HazardFree.Properties (oracle) using (hf-∷⁻-∀)
open import Functional.Script.Properties (oracle) using (DisjointBuild ; Cons ; dsj-≡)
open import Functional.Script.Hazard (oracle) using (Hazard ; HazardFree ; FileInfo ; ReadWrite ; WriteWrite ; Speculative ; :: ; cmdWrites ; filesRead ; files ; cmdReads ; ¬SpeculativeHazard ; save ; getN ; hazardContradiction)
-- open import Functional.Script.Hazard.Properties (oracle) using (hf-≡)
open import Data.Empty using (⊥ ; ⊥-elim)



data MemoryProperty : Memory -> Set where
 []   : MemoryProperty []
 Cons : {mm : Memory} (x : Cmd) -> (sys : System) -> (∀ f₁ → f₁ ∈ cmdReads sys x -> sys f₁ ≡ St.run oracle x sys f₁) -> MemoryProperty mm -> MemoryProperty ((x , map (λ f₁ → f₁ , (St.run oracle x sys) f₁) (cmdReadWrites x sys)) ∷ mm)
 

getProperty : {mm : Memory} (x : Cmd) -> MemoryProperty mm -> (x∈ : x ∈ map proj₁ mm) -> ∃[ sys ](get x mm x∈ ≡ map (λ f₁ → f₁ , (St.run oracle x sys) f₁) (cmdReadWrites x sys) × ∀ f₁ → f₁ ∈ cmdReads sys x -> sys f₁ ≡ St.run oracle x sys f₁)
getProperty x (Cons x₁ sys ∀₁ mp) x∈ with x ≟ x₁
... | yes x≡x₁ = sys , cong (λ x₂ → map (λ f₁ → f₁ , foldr extend sys (proj₂ (proj₁ (oracle x₂) sys)) f₁) (cmdReadWrites x₂ sys)) (sym x≡x₁) , λ f₁ x₂ → subst (λ x₃ → sys f₁ ≡ St.run oracle x₃ sys f₁) (sym x≡x₁) (∀₁ f₁ (subst (λ x₃ → f₁ ∈ map proj₁ (proj₁ (proj₁ (oracle x₃) sys))) x≡x₁ x₂))
... | no ¬x≡x₁ = getProperty x mp (tail ¬x≡x₁ x∈)

lemma1 : ∀ (s : System) {s₁} {x} ls ls₁ → All (λ (f₁ , v₁) → s f₁ ≡ v₁) ls → ls ≡ map (λ f₁ → f₁ , (St.run oracle x s₁) f₁) ls₁ → All (λ f₁ → s f₁ ≡ St.run oracle x s₁ f₁) ls₁
lemma1 s [] [] all₁ ≡₁ = All.[]
lemma1 s (x₁ ∷ ls) (x ∷ ls₁) (px All.∷ all₁) ≡₁ with ∷-injective ≡₁
... | x₁≡x , ≡₂ = (trans (subst (λ x₂ → s x₂ ≡ proj₂ x₁) (,-injectiveˡ x₁≡x) px) (,-injectiveʳ x₁≡x)) All.∷ (lemma1 s ls ls₁ all₁ ≡₂)

{- Want to prove that system will be the same whether or not we run the command; -}
{- If a command's inputs and outputs are unchanged from when it was last run,
 then running it will have no effect. -}
noEffect : ∀ {s} {mm} x → MemoryProperty mm → (x∈ : x ∈ map proj₁ mm) → All (λ (f₁ , v₁) → s f₁ ≡ v₁) (get x mm x∈) → ∀ f₁ → s f₁ ≡ St.run oracle x s f₁
noEffect {s} {mm} x mp x∈ all₁ f₁ with getProperty x mp x∈
... | s₁ , get≡ , ∀₁ with f₁ ∈? cmdWrites s x
... | no f₁∉ = St.lemma3 f₁ (proj₂ (proj₁ (oracle x) s)) f₁∉
{- If we write to it we know we don't read from it.  
   Need to prove the result of running x is the same in s and s₁
-}
... | yes f₁∈ with lemma1 s (get x mm x∈) (cmdReadWrites x s₁) all₁ get≡
... | all₂ with proj₂ (oracle x) s₁ s λ f₂ x₁ → trans (∀₁ f₂ x₁) (sym (lookup all₂ (∈-++⁺ˡ x₁)))
... | ≡results with subst (λ x₁ → f₁ ∈ x₁) (sym (cong (map proj₁ ∘ proj₂) ≡results)) f₁∈
... | f₁∈x-s₁ = trans (lookup all₂ (∈-++⁺ʳ (cmdReads s₁ x) f₁∈x-s₁))
                      (subst (λ x₁ → foldr extend s₁ (proj₂ (proj₁ (oracle x) s₁)) f₁ ≡ foldr extend s x₁ f₁) (cong proj₂ ≡results)
                        (St.lemma4 (proj₂ (proj₁ (oracle x) s₁)) f₁ f₁∈x-s₁))


doRunSoundness : ∀ st ls st₁ ls₁ b x → doRunWError b (st , ls) x ≡ inj₂ (st₁ , ls₁) → doRun st x ≡ st₁
doRunSoundness st ls st₁ ls₁ b x ≡₁ with checkHazard (proj₁ st) x b ls
... | nothing = cong proj₁ (inj₂-injective ≡₁)

runSoundness : ∀ st ls st₁ ls₁ b x → runWError b (st , ls) x ≡ inj₂ (st₁ , ls₁) → run st x ≡ st₁
runSoundness st ls st₁ ls₁ b x ≡₁ with run? x st
... | false = cong proj₁ (inj₂-injective ≡₁)
... | true = doRunSoundness st ls st₁ ls₁ b x ≡₁

soundness : ∀ st ls st₁ ls₁ b₁ b₂ → execWError (st , ls) b₁ b₂ ≡ inj₂ (st₁ , ls₁) → exec st b₁ ≡ st₁
soundness st ls st₁ ls₁ [] b₂ ≡₁ = cong proj₁ (inj₂-injective ≡₁)
soundness st ls st₁ ls₁ (x ∷ b₁) b₂ ≡₁ with runWError b₂ (st , ls) x | inspect (runWError b₂ (st , ls)) x
... | inj₂ (st₂ , ls₂) | [ ≡₂ ] with run? x st | runSoundness st ls st₂ ls₂ b₂ x ≡₂
... | false | st≡st₂ with soundness st₂ ls₂ st₁ ls₁ b₁ b₂ ≡₁
... | a = subst (λ x₁ → exec x₁ b₁ ≡ st₁) (sym st≡st₂) a
soundness st ls st₁ ls₁ (x ∷ b₁) b₂ ≡₁ | inj₂ (st₂ , ls₂) | [ ≡₂ ] | true | ≡st₂ with soundness st₂ ls₂ st₁ ls₁ b₁ b₂ ≡₁
... | a = subst (λ x₁ → exec x₁ b₁ ≡ st₁) (sym ≡st₂) a


-- runWError ≡ run if runWError ≡ inj₂

-- prove if no errors ; do run and dorun check are the same ; aka give same system

-- completeness, does rattle actually work for pieces of software?

-- if there is no hazard then run with error produces right; use hazardfree evidence
-- won't tell you there is a hazard when there isn't a hazard
completeness : ∀ st₁ ls₁ b₁ b₂ → DisjointBuild (proj₁ st₁) b₁ → HazardFree (proj₁ st₁) b₁ b₂ ls₁ → MemoryProperty (proj₂ st₁) → ∃[ st ](∃[ ls ](execWError (st₁ , ls₁) b₁ b₂ ≡ inj₂ (st , ls)))
completeness st ls [] _ dsb hf mp = st , ls , refl
completeness st@(s , mm) ls (x ∷ b₁) b₂ (Cons .x ds .b₁ dsb) (:: .s .ls .x .b₁ .b₂ ¬sh dsj hf) mp with x ∈? map proj₁ mm
... | yes x∈ with maybeAll {s} (get x mm x∈)
... | nothing with checkHazard s x b₂ ls
... | nothing = completeness (St.run oracle x s , St.save x ((cmdReads s x) ++ (cmdWrites s x)) (St.run oracle x s) mm) (save x (cmdReads s x) (cmdWrites s x) ls) b₁ b₂ dsb hf (MemoryProperty.Cons x s (λ f₁ x₂ → St.lemma3 f₁ (proj₂ (proj₁ (oracle x) s)) λ x₃ → ds (x₂ , x₃)) mp)
... | just hz = ⊥-elim (hazardContradiction s x b₂ ls hz dsj ¬sh)
completeness st@(s , mm) ls (x ∷ b₁) b₂ (Cons .x x₁ .b₁ dsb) (:: .s .ls .x .b₁ .b₂ ¬sh dsj hf) mp | yes x∈ | just all₁ with noEffect x mp x∈ all₁
... | ∀₁ = completeness st ls b₁ b₂ (dsj-≡ (St.run oracle x s) s b₁ ∀₁ dsb) {!!} mp


completeness st@(s , mm) ls (x ∷ b₁) b₂ (Cons .x ds .b₁ dsb) (:: .s .ls .x .b₁ .b₂ ¬sh dsj hf) mp | no x∉ with checkHazard s x b₂ ls
... | nothing = completeness (St.run oracle x s , St.save x ((cmdReads s x) ++ (cmdWrites s x)) (St.run oracle x s) mm) (save x (cmdReads s x) (cmdWrites s x) ls) b₁ b₂ dsb hf (MemoryProperty.Cons x s (λ f₁ x₂ → St.lemma3 f₁ (proj₂ (proj₁ (oracle x) s)) λ x₃ → ds (x₂ , x₃)) mp)
... | just hz = ⊥-elim (hazardContradiction s x b₂ ls hz dsj ¬sh)

{-
correct : ∀ sys b ls → HazardFree sys b ls → exec (sys , []) b ≡ exec (exec (sys , []) b) b
correct = {!!}
-}

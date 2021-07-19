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
open import Functional.Script.Properties (oracle) using (DisjointBuild ; Cons)
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



doRunSoundness : ∀ st ls st₁ ls₁ b x → doRunWError b (st , ls) x ≡ inj₂ (st₁ , ls₁) → doRun st x ≡ st₁
doRunSoundness st ls st₁ ls₁ b x ≡₁ with checkHazard (proj₁ st) x b ls
... | nothing = {!!}

{-doRunSoundness {sys₀} {st} {st₁} {b} {rf} {fi} x {fi₁} ≡₁ with hasHazard st fi x rf
... | nothing = cong proj₁ (inj₂-injective ≡₁) -}

runSoundness : ∀ st ls st₁ ls₁ b x → runWError b (st , ls) x ≡ inj₂ (st₁ , ls₁) → run st x ≡ st₁
runSoundness st ls st₁ ls₁ b x ≡₁ with run? x st
... | false = cong proj₁ (inj₂-injective ≡₁)
... | true = {!!}
{-
runSoundness {sys₀} {st} {st₁} {b} {rf} {fi} x {fi₁} ≡₁ with run? x st
... | true =doRunSoundness {sys₀} {st} {st₁} {b} {rf} {fi} x {fi₁} {!!}
... | false = cong proj₁ (inj₂-injective ≡₁)
-}

soundness : ∀ st ls st₁ ls₁ b₁ b₂ → execWError (st , ls) b₁ b₂ ≡ inj₂ (st₁ , ls₁) → exec st b₁ ≡ st₁
soundness st ls st₁ ls₁ [] b₂ ≡₁ = cong proj₁ (inj₂-injective ≡₁)
soundness st ls st₁ ls₁ (x ∷ b₁) b₂ ≡₁ with runWError b₂ (st , ls) x
... | inj₂ (st₂ , ls₂) with run? x st
... | true = {!!}
... | false = soundness st ls st₁ ls₁ b₁ b₂ {!!}

{-
soundness [] ≡₁ = cong proj₁ (inj₂-injective {!!})
soundness {sys₀} {st} {st₁} {b₁} {b₂} {rf} {fi} {fi₁} (x ∷ b) ≡₁ with runWError st fi x rf | inspect (runWError st fi x) rf
... | inj₂ (st₂ , fi₂) | [ ≡₂ ] with run? x st | runSoundness {sys₀} {st} {st₂} {b₁} {rf} {fi} x {fi₂} ≡₂
... | false | st≡st₂ = soundness b (subst (λ x₁ → execWError (x₁ , fi₂) b rf ≡ _) (sym st≡st₂) {!!})
... | true | ≡₃ = soundness b (subst (λ x₁ → execWError (x₁ , fi₂) b rf ≡ _) (sym ≡₃) {!!})
-}


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
completeness st@(s , mm) ls (x ∷ b₁) b₂ (Cons .x x₁ .b₁ dsb) (:: .s .ls .x .b₁ .b₂ ¬sh dsj hf) mp | yes x∈ | just all₁ with getProperty x mp x∈
... | s₁ , get≡ , ∀₁ = completeness st ls b₁ b₂ {!!} {!!} mp
        -- (hf-≡ [] (St.run oracle x s) s {!!} hf)
completeness st@(s , mm) ls (x ∷ b₁) b₂ (Cons .x ds .b₁ dsb) (:: .s .ls .x .b₁ .b₂ ¬sh dsj hf) mp | no x∉ with checkHazard s x b₂ ls
... | nothing = completeness (St.run oracle x s , St.save x ((cmdReads s x) ++ (cmdWrites s x)) (St.run oracle x s) mm) (save x (cmdReads s x) (cmdWrites s x) ls) b₁ b₂ dsb hf (MemoryProperty.Cons x s (λ f₁ x₂ → St.lemma3 f₁ (proj₂ (proj₁ (oracle x) s)) λ x₃ → ds (x₂ , x₃)) mp)
... | just hz = ⊥-elim (hazardContradiction s x b₂ ls hz dsj ¬sh)

{-
correct : ∀ sys b ls → HazardFree sys b ls → exec (sys , []) b ≡ exec (exec (sys , []) b) b
correct = {!!}
-}


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
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Functional.Rattle.Exec (oracle) using (execWError ; runWError ; run ; doRun ; exec ; doRunWError ; checkHazard ; g₂)
open import Functional.Build using (Build)
open import Data.Sum using (inj₂ ; from-inj₂ ; inj₁ )
open import Data.Sum.Properties using (inj₂-injective)
open import Functional.Script.Exec (oracle) as Script hiding (exec)
open import Functional.Script.Properties (oracle) using (DisjointBuild ; Cons ; dsj-≡)

open import Functional.Script.Hazard (oracle) using (Hazard ; HazardFree ; FileInfo ; :: ; cmdWrites ; cmdReads ; ¬SpeculativeHazard ; save ; hazardContradiction)

open import Functional.Script.Hazard.Properties (oracle) using (hf-≡)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using (_∷_)



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


doRunSoundness : ∀ st ls {st₁} {ls₁} b x uls ub {uls₁} {≡₁} → doRunWError b (st , ls) x uls ub ≡ inj₂ (st₁ , ls₁ , uls₁ , ≡₁) → doRun st x ≡ st₁
doRunSoundness st ls b x uls ub ≡₁ with checkHazard (proj₁ st) x b ls uls ub
... | nothing = cong proj₁ (inj₂-injective ≡₁)

runSoundness : ∀ st ls st₁ ls₁ b x uls ub x∉ls {uls₁} {≡₁} → runWError b (st , ls) x uls ub x∉ls ≡ inj₂ (st₁ , ls₁ , uls₁ , ≡₁) → run st x ≡ st₁
runSoundness st ls st₁ ls₁ b x uls ub x∉ls ≡₁ with run? x st
... | false = cong proj₁ (inj₂-injective ≡₁)
... | true = doRunSoundness st ls b x (g₂ (map proj₁ ls) x∉ls ∷ uls) ub ≡₁

soundness : ∀ {st₁} {ls₁} st ls → (b₁ b₂ : Build) → (ub₁ : Unique b₁) → (ub₂ : Unique b₂) → (uls : Unique (map proj₁ ls)) → (dsj : Disjoint b₁ (map proj₁ ls)) → execWError (st , ls) b₁ b₂ ub₁ ub₂ uls dsj ≡ inj₂ (st₁ , ls₁) → exec st b₁ ≡ st₁
soundness st ls [] b₂ ub₁ ub₂ uls dsj ≡₁ = cong proj₁ (inj₂-injective ≡₁)
soundness st ls (x ∷ b₁) b₂ (px ∷ ub₁) ub₂ uls dsj ≡₁ with runWError b₂ (st , ls) x uls ub₂ (λ x₁ → dsj (here refl , x₁)) | inspect (runWError b₂ (st , ls) x uls ub₂) (λ x₁ → dsj (here refl , x₁))
... | inj₂ (st₂ , ls₂ , uls₂ , inj₁ ls₂≡ls) | [ ≡₂ ] with runSoundness st ls st₂ ls₂ b₂ x uls ub₂ (λ x₁ → dsj (here refl , x₁)) ≡₂
... | ≡st₂ = subst (λ x₁ → exec x₁ b₁ ≡ _) (sym ≡st₂) (soundness st₂ ls₂ b₁ b₂ ub₁ ub₂ uls₂ (λ x₁ → dsj (there (proj₁ x₁) , subst (λ x₂ → _ ∈ x₂) ls₂≡ls (proj₂ x₁))) ≡₁)
soundness st ls (x ∷ b₁) b₂ (px ∷ ub₁) ub₂ uls dsj ≡₁ | inj₂ (st₂ , ls₂ , uls₂ , inj₂ ls₂≡x∷ls) | [ ≡₂ ] with runSoundness st ls st₂ ls₂ b₂ x uls ub₂ (λ x₁ → dsj (here refl , x₁)) ≡₂
... | ≡st₂ = subst (λ x₁ → exec x₁ b₁ ≡ _) (sym ≡st₂) (soundness st₂ ls₂ b₁ b₂ ub₁ ub₂ uls₂ (λ x₁ → dsj (there (proj₁ x₁) , g₁ (proj₂ x₁) ls₂≡x∷ls λ v≡x → lookup px (proj₁ x₁) (sym v≡x))) ≡₁)
  where g₁ : ∀ {v} {ls₁} {ls₂} {x} → v ∈ ls₁ → ls₁ ≡ x ∷ ls₂ → ¬ v ≡ x → v ∈ ls₂
        g₁ v∈ls₁ ls₁≡x∷ls₂ ¬v≡x = tail ¬v≡x (subst (λ x₁ → _ ∈ x₁) ls₁≡x∷ls₂ v∈ls₁)


-- prove if no errors ; do run and dorun check are the same ; aka give same system

-- completeness, does rattle actually work for pieces of software?

-- if there is no hazard then run with error produces right; use hazardfree evidence
-- won't tell you there is a hazard when there isn't a hazard

completeness : ∀ st₁ ls₁ b₁ b₂ → (ub₁ : Unique b₁) → (ub₂ : Unique b₂) →  (uls : Unique (map proj₁ ls₁)) → (dsj : Disjoint b₁ (map proj₁ ls₁)) → DisjointBuild (proj₁ st₁) b₁ → HazardFree (proj₁ st₁) b₁ b₂ ls₁ → MemoryProperty (proj₂ st₁) → ∃[ st ](∃[ ls ](execWError (st₁ , ls₁) b₁ b₂ ub₁ ub₂ uls dsj ≡ inj₂ (st , ls)))
completeness st ls [] _ ub₁ ub₂ uls dsj dsb hf mp = st , ls , refl
completeness st@(s , mm) ls (x ∷ b₁) b₂ (px ∷ ub₁) ub₂ uls dsj₁ (Cons .x ds .b₁ dsb) (:: .s .ls .x .b₁ .b₂ ¬sh dsj hf) mp with x ∈? map proj₁ mm
... | yes x∈ with maybeAll {s} (get x mm x∈)
... | nothing with checkHazard s x b₂ ls (g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls) ub₂
... | just hz = ⊥-elim (hazardContradiction s x b₂ ls hz dsj ¬sh)
... | nothing = completeness (St.run oracle x s , St.save x ((cmdReads s x) ++ (cmdWrites s x)) (St.run oracle x s) mm) (save x (cmdReads s x) (cmdWrites s x) ls) b₁ b₂ ub₁ ub₂ (g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls) dsj₂ dsb hf (MemoryProperty.Cons x s (λ f₁ x₂ → St.lemma3 f₁ (proj₂ (proj₁ (oracle x) s)) λ x₃ → ds (x₂ , x₃)) mp)
  where dsj₂ : Disjoint b₁ (x ∷ map proj₁ ls)
        dsj₂ = λ x₁ → dsj₁ (there (proj₁ x₁) , tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))


completeness st@(s , mm) ls (x ∷ b₁) b₂ (px ∷ ub₁) ub₂ uls dsj₁ (Cons .x x₁ .b₁ dsb) (:: .s .ls .x .b₁ .b₂ ¬sh dsj hf) mp | yes x∈ | just all₁ with noEffect x mp x∈ all₁
... | ∀₁ = completeness st ls b₁ b₂ ub₁ ub₂ uls dsj₂ (dsj-≡ (St.run oracle x s) s b₁ ∀₁ dsb) (hf-≡ s [] b₁ {!!} ∀₁ hf) mp
  where dsj₂ : Disjoint b₁ (map proj₁ ls)
        dsj₂ = λ x₂ → dsj₁ (there (proj₁ x₂) , proj₂ x₂)
        
completeness st@(s , mm) ls (x ∷ b₁) b₂ (px ∷ ub₁) ub₂ uls dsj₁ (Cons .x ds .b₁ dsb) (:: .s .ls .x .b₁ .b₂ ¬sh dsj hf) mp | no x∉ with checkHazard s x b₂ ls (g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls) ub₂
... | nothing = completeness (St.run oracle x s , St.save x ((cmdReads s x) ++ (cmdWrites s x)) (St.run oracle x s) mm) (save x (cmdReads s x) (cmdWrites s x) ls) b₁ b₂ ub₁ ub₂ (g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls) dsj₂ dsb hf (MemoryProperty.Cons x s (λ f₁ x₂ → St.lemma3 f₁ (proj₂ (proj₁ (oracle x) s)) λ x₃ → ds (x₂ , x₃)) mp)
  where dsj₂ : Disjoint b₁ (x ∷ map proj₁ ls)
        dsj₂ = λ x₁ → dsj₁ (there (proj₁ x₁) , tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))

... | just hz = ⊥-elim (hazardContradiction s x b₂ ls hz dsj ¬sh)



{-
correct : ∀ sys b ls → HazardFree sys b ls → exec (sys , []) b ≡ exec (exec (sys , []) b) b
correct = {!!}
-}

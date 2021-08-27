\begin{code}[hide]
open import Functional.State as St using (F ; System ; Memory ; Cmd ; trace ; extend ; State ; run-≡)

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
open import Functional.Rattle.Exec (oracle) using (execWError ; runWError ; run ; doRun ; exec ; doRunWError ; checkHazard ; g₂ ; UniqueEvidence)
open import Functional.Build using (Build)
open import Data.Sum using (inj₂ ; from-inj₂ ; inj₁ ; _⊎_)
open import Data.Sum.Properties using (inj₂-injective)
open import Functional.Script.Exec (oracle) as Script hiding (exec)
open import Functional.Script.Properties (oracle) using (DisjointBuild ; Cons ; dsj-≡)

open import Functional.Script.Hazard (oracle) using (Hazard ; HazardFree ; FileInfo ; :: ; cmdWrites ; cmdReads ; ¬SpeculativeHazard ; save ; hazardContradiction ; ∃Hazard)

open import Functional.Script.Hazard.Properties (oracle) using (hf-still)
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
noEffect : ∀ {s₁} {s₂ : System} {mm} x → (∀ f₁ → s₁ f₁ ≡ s₂ f₁) → MemoryProperty mm → (x∈ : x ∈ map proj₁ mm) → All (λ (f₁ , v₁) → s₂ f₁ ≡ v₁) (get x mm x∈) → ∀ f₁ → s₂ f₁ ≡ St.run oracle x s₁ f₁
noEffect {s₁} {s₂} {mm} x ∀₁ mp x∈ all₁ f₁ with getProperty x mp x∈
... | s₃ , get≡ , ∀₂ with f₁ ∈? cmdWrites s₁ x
... | no f₁∉ = trans (sym (∀₁ f₁)) (St.lemma3 f₁ (proj₂ (proj₁ (oracle x) s₁)) f₁∉)
... | yes f₁∈ with lemma1 s₂ (get x mm x∈) (cmdReadWrites x s₃) all₁ get≡
... | all₂ with proj₂ (oracle x) s₃ s₁ λ f₂ x₁ → sym (trans (∀₁ f₂) (trans (lookup all₂ (∈-++⁺ˡ x₁)) (sym (∀₂ f₂ x₁))))
... | ≡₁ = trans (lookup all₂ (∈-++⁺ʳ (cmdReads s₃ x) f₁∈₁))
                 (subst (λ x₁ → foldr extend s₃ x₁ f₁ ≡ foldr extend s₁ (proj₂ (proj₁ (oracle x) s₁)) f₁)
                        (sym (cong proj₂ ≡₁))
                        (St.lemma4 (proj₂ (proj₁ (oracle x) s₁)) f₁ f₁∈))
  where f₁∈₁ : f₁ ∈ cmdWrites s₃ x
        f₁∈₁ = subst (λ ls → f₁ ∈ ls) (sym (cong (map proj₁ ∘ proj₂) ≡₁)) f₁∈


doRunSoundness : ∀ st ls {st₁} {ls₁} b x uls ub {uls₁} {≡₁} → doRunWError b (st , ls) x uls ub ≡ inj₂ (st₁ , ls₁ , uls₁ , ≡₁) → doRun st x ≡ st₁
doRunSoundness st ls b x uls ub ≡₁ with checkHazard (proj₁ st) x b ls uls ub
... | nothing = cong proj₁ (inj₂-injective ≡₁)

runSoundness : ∀ st ls st₁ ls₁ b x uls ub x∉ls {uls₁} {≡₁} → runWError b (st , ls) x uls ub x∉ls ≡ inj₂ (st₁ , ls₁ , uls₁ , ≡₁) → run st x ≡ st₁
runSoundness st ls st₁ ls₁ b x uls ub x∉ls ≡₁ with run? x st
... | false = cong proj₁ (inj₂-injective ≡₁)
... | true = doRunSoundness st ls b x (g₂ (map proj₁ ls) x∉ls ∷ uls) ub ≡₁
\end{code}

\newcommand{\soundness}{%
\begin{code}
soundness : ∀ {st₁} {ls₁} st ls → (b₁ b₂ : Build) → (ue : UniqueEvidence b₁ b₂ (map proj₁ ls)) → execWError (st , ls) b₁ b₂ ue ≡ inj₂ (st₁ , ls₁) → exec st b₁ ≡ st₁
\end{code}}
\begin{code}[hide]
soundness st ls [] b₂ (ub₁ , ub₂ , uls , dsj) ≡₁ = cong proj₁ (inj₂-injective ≡₁)
soundness st ls (x ∷ b₁) b₂ ((px ∷ ub₁) , ub₂ , uls , dsj) ≡₁ with runWError b₂ (st , ls) x uls ub₂ (λ x₁ → dsj (here refl , x₁)) | inspect (runWError b₂ (st , ls) x uls ub₂) (λ x₁ → dsj (here refl , x₁))
... | inj₂ (st₂ , ls₂ , uls₂ , inj₁ ls₂≡ls) | [ ≡₂ ] with runSoundness st ls st₂ ls₂ b₂ x uls ub₂ (λ x₁ → dsj (here refl , x₁)) ≡₂
... | ≡st₂ = subst (λ x₁ → exec x₁ b₁ ≡ _) (sym ≡st₂) (soundness st₂ ls₂ b₁ b₂ (ub₁ , ub₂ , uls₂ , λ x₁ → dsj (there (proj₁ x₁) , subst (λ x₂ → _ ∈ x₂) ls₂≡ls (proj₂ x₁))) ≡₁)
soundness st ls (x ∷ b₁) b₂ ((px ∷ ub₁) , ub₂ , uls , dsj) ≡₁ | inj₂ (st₂ , ls₂ , uls₂ , inj₂ ls₂≡x∷ls) | [ ≡₂ ] with runSoundness st ls st₂ ls₂ b₂ x uls ub₂ (λ x₁ → dsj (here refl , x₁)) ≡₂
... | ≡st₂ = subst (λ x₁ → exec x₁ b₁ ≡ _) (sym ≡st₂) (soundness st₂ ls₂ b₁ b₂ (ub₁ , ub₂ , uls₂ , λ x₁ → dsj (there (proj₁ x₁) , g₁ (proj₂ x₁) ls₂≡x∷ls λ v≡x → lookup px (proj₁ x₁) (sym v≡x))) ≡₁)
  where g₁ : ∀ {v} {ls₁} {ls₂} {x} → v ∈ ls₁ → ls₁ ≡ x ∷ ls₂ → ¬ v ≡ x → v ∈ ls₂
        g₁ v∈ls₁ ls₁≡x∷ls₂ ¬v≡x = tail ¬v≡x (subst (λ x₁ → _ ∈ x₁) ls₁≡x∷ls₂ v∈ls₁)
\end{code}

\begin{code}[hide]
-- prove if no errors ; do run and dorun check are the same ; aka give same system

-- completeness, does rattle actually work for pieces of software?

-- if there is no hazard then run with error produces right; use hazardfree evidence
-- won't tell you there is a hazard when there isn't a hazard
\end{code}

\newcommand{\completeness}{%
\begin{code}
completeness : ∀ st₁ ls₁ b₁ b₂ → (ue : UniqueEvidence b₁ b₂ (map proj₁ ls₁)) → DisjointBuild (proj₁ st₁) b₁ → HazardFree (proj₁ st₁) b₁ b₂ ls₁ → MemoryProperty (proj₂ st₁) → ∃[ st ](∃[ ls ](execWError (st₁ , ls₁) b₁ b₂ ue ≡ inj₂ (st , ls)))
\end{code}}
\begin{code}[hide]
completeness st ls [] _ (ub₁ , ub₂ , uls , dsj) dsb hf mp = st , ls , refl
completeness st@(s , mm) ls (x ∷ b₁) b₂ ((px ∷ ub₁) , ub₂ , uls , dsj₁) (Cons .x ds .b₁ dsb) (:: .s .ls .x .b₁ .b₂ ¬sh dsj hf) mp with x ∈? map proj₁ mm
... | yes x∈ with maybeAll {s} (get x mm x∈)
... | nothing with checkHazard s x b₂ ls (g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls) ub₂
... | just hz = ⊥-elim (hazardContradiction s x b₂ ls hz dsj ¬sh)
... | nothing = completeness st₂ ls₂ b₁ b₂ (ub₁ , ub₂ , uls₂ , dsj₂) dsb hf mp₂
  where dsj₂ : Disjoint b₁ (x ∷ map proj₁ ls)
        dsj₂ = λ x₁ → dsj₁ (there (proj₁ x₁) , tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
        st₂ : State
        st₂ = St.run oracle x s , St.save x ((cmdReads s x) ++ (cmdWrites s x)) (St.run oracle x s) mm
        ls₂ : FileInfo
        ls₂ = save x (cmdReads s x) (cmdWrites s x) ls
        uls₂ : Unique (x ∷ map proj₁ ls)
        uls₂ = g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls
        mp₂ : MemoryProperty (proj₂ st₂)
        mp₂ = MemoryProperty.Cons x s (λ f₁ x₂ → St.lemma3 f₁ (proj₂ (proj₁ (oracle x) s)) λ x₃ → ds (x₂ , x₃)) mp

completeness st@(s , mm) ls (x ∷ b₁) b₂ ((px ∷ ub₁) , ub₂ , uls , dsj₁) (Cons .x x₁ .b₁ dsb) (:: .s .ls .x .b₁ .b₂ ¬sh dsj hf) mp | yes x∈ | just all₁ with noEffect x (λ f₁ → refl) mp x∈ all₁
... | ∀₁ = completeness st ls b₁ b₂ (ub₁ , ub₂ , uls , dsj₃) (dsj-≡ (St.run oracle x s) s b₁ ∀₁ dsb) hf₂ mp
  where dsj₃ : Disjoint b₁ (map proj₁ ls)
        dsj₃ = λ x₂ → dsj₁ (there (proj₁ x₂) , proj₂ x₂)
        dsj₂ : Disjoint b₁ (x ∷ map proj₁ ls)
        dsj₂ = λ x₁ → dsj₁ (there (proj₁ x₁) , tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
        uls₂ : Unique (x ∷ map proj₁ ls)
        uls₂ = g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls
        hf₂ : HazardFree s b₁ b₂ ls
        hf₂ = hf-still b₁ [] ((x , cmdReads s x , cmdWrites s x) ∷ []) ls (λ f₁ x₂ → sym (∀₁ f₁)) ub₁ uls₂ dsj₂ hf
        
completeness st@(s , mm) ls (x ∷ b₁) b₂ ((px ∷ ub₁) , ub₂ , uls , dsj₁) (Cons .x ds .b₁ dsb) (:: .s .ls .x .b₁ .b₂ ¬sh dsj hf) mp | no x∉ with checkHazard s x b₂ ls (g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls) ub₂
... | just hz = ⊥-elim (hazardContradiction s x b₂ ls hz dsj ¬sh)
... | nothing = completeness (St.run oracle x s , St.save x ((cmdReads s x) ++ (cmdWrites s x)) (St.run oracle x s) mm) (save x (cmdReads s x) (cmdWrites s x) ls) b₁ b₂ (ub₁ , ub₂ , (g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls) , dsj₂) dsb hf (MemoryProperty.Cons x s (λ f₁ x₂ → St.lemma3 f₁ (proj₂ (proj₁ (oracle x) s)) λ x₃ → ds (x₂ , x₃)) mp)
  where dsj₂ : Disjoint b₁ (x ∷ map proj₁ ls)
        dsj₂ = λ x₁ → dsj₁ (there (proj₁ x₁) , tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
\end{code}

\newcommand{\lemma1}{%
\begin{code}
script≡rattle : ∀ {s₁} {s₂} mm b₁ → (∀ f₁ → s₁ f₁ ≡ s₂ f₁) → DisjointBuild s₂ b₁ → MemoryProperty mm → (∀ f₁ → Script.exec s₁ b₁ f₁ ≡ proj₁ (exec (s₂ , mm) b₁) f₁)
\end{code}}
\begin{code}[hide]
script≡rattle mm [] ∀₁ dsb mp = ∀₁ 
script≡rattle {s₁} {s₂} mm (x ∷ b₁) ∀₁ (Cons .x dsj .b₁ dsb) mp f₁ with x ∈? map proj₁ mm
... | no x∉ = script≡rattle {St.run oracle x s₁} {St.run oracle x s₂} (St.save x (cmdReads s₂ x ++ cmdWrites s₂ x) (St.run oracle x s₂) mm) b₁ (run-≡ {oracle} x ∀₁) dsb mp₁ f₁
  where mp₁ : MemoryProperty (St.save x (cmdReads s₂ x ++ cmdWrites s₂ x) (St.run oracle x s₂) mm)
        mp₁ = Cons x s₂ (λ f₂ x₁ → St.lemma3 f₂ (proj₂ (proj₁ (oracle x) s₂)) λ x₂ → dsj (x₁ , x₂)) mp
... | yes x∈ with maybeAll {s₂} (get x mm x∈)
... | nothing = script≡rattle {St.run oracle x s₁} {St.run oracle x s₂} (St.save x (cmdReads s₂ x ++ cmdWrites s₂ x) (St.run oracle x s₂) mm) b₁ (run-≡ {oracle} x ∀₁) dsb mp₁ f₁
  where mp₁ : MemoryProperty (St.save x (cmdReads s₂ x ++ cmdWrites s₂ x) (St.run oracle x s₂) mm)
        mp₁ = Cons x s₂ (λ f₂ x₁ → St.lemma3 f₂ (proj₂ (proj₁ (oracle x) s₂)) λ x₂ → dsj (x₁ , x₂)) mp
... | just all₁ = script≡rattle {St.run oracle x s₁} {s₂} mm b₁ ∀₂ (dsj-≡ (St.run oracle x s₂) s₂ b₁ ∀₃ dsb) mp f₁
  where ∀₂ : ∀ f₁ → St.run oracle x s₁ f₁ ≡ s₂ f₁
        ∀₂ f₁ = sym (noEffect x ∀₁ mp x∈ all₁ f₁)
        ∀₃ : ∀ f₁ → s₂ f₁ ≡ St.run oracle x s₂ f₁
        ∀₃ = noEffect x (λ f₂ → refl) mp x∈ all₁
\end{code}

\begin{code}[hide]
-- correctness is if you have any build then either you get the right answer (the one the script gave) or you get an error and there was a hazard.
\end{code}
\newcommand{\correct}{%
\begin{code}
correct : ∀ b₁ b₂ s mm ls → DisjointBuild s b₁ → MemoryProperty mm → (ue : UniqueEvidence b₁ b₂ (map proj₁ ls)) → ¬ HazardFree s b₁ b₂ ls ⊎ ∃[ st₁ ](execWError ((s , mm) , ls) b₁ b₂ ue ≡ inj₂ st₁ × ∀ f₁ → proj₁ (proj₁ st₁) f₁ ≡ Script.exec s b₁ f₁)
correct b₁ b₂ s mm ls dsb mp ue with execWError ((s , mm) , ls) b₁ b₂ ue | inspect (execWError ((s , mm) , ls) b₁ b₂) ue 
... | inj₁ hz | [ ≡₁ ] = inj₁ g₁
  where g₁ : HazardFree s b₁ b₂ ls → ⊥
        g₁ hf with completeness (s , mm) ls b₁ b₂ ue dsb hf mp
        ... | a , fst , ≡₂ = contradiction (trans (sym ≡₁) ≡₂) λ ()
... | inj₂ (st , _) | [ ≡₁ ] = inj₂ ((st , _) , refl , λ f₁ → sym (trans (script≡rattle mm b₁ (λ f₂ → refl) dsb mp f₁) (cong-app (cong proj₁ (soundness (s , mm) ls b₁ b₂ ue ≡₁)) f₁)))
\end{code}}

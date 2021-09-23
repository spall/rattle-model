\begin{code}[hide]
open import Functional.State using (Oracle ; FileSystem ; Memory ; Cmd ; extend ; State ; save)

module Functional.Rattle.Properties (oracle : Oracle) where

open import Agda.Builtin.Equality

open import Functional.State.Helpers (oracle) as St using (cmdReadNames ; cmdWriteNames)
open import Functional.State.Properties (oracle) using (lemma3 ; lemma4 ; run-≡)
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
open import Functional.Rattle.Exec (oracle) using (rattle ; runWError ; runR ; doRun ; rattle_unchecked ; doRunWError ; checkHazard ; g₂)
open import Functional.Build (oracle) using (Build ; UniqueEvidence ; PreCond ; DisjointBuild ; Cons)
open import Data.Sum using (inj₂ ; from-inj₂ ; inj₁ ; _⊎_)
open import Data.Sum.Properties using (inj₂-injective)
open import Functional.Script.Exec (oracle) as Script
open import Functional.Script.Properties (oracle) using (dsj-≡)
open import Functional.Script.Proofs (oracle) using (reordered ; reordered≡)

open import Functional.Script.Hazard (oracle) using (Hazard ; HazardFree ; FileInfo ; :: ; ¬SpeculativeHazard ; hazardContradiction ; ∃Hazard ; [] ; HFC ; hazardfree?) renaming (save to rec)

open import Functional.Script.Hazard.Properties (oracle) using (hf-still)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)



data MemoryProperty : Memory -> Set where
 []   : MemoryProperty []
 Cons : {mm : Memory} (x : Cmd) -> (sys : FileSystem) -> (∀ f₁ → f₁ ∈ cmdReadNames x sys -> sys f₁ ≡ St.run x sys f₁) -> MemoryProperty mm -> MemoryProperty ((x , map (λ f₁ → f₁ , (St.run x sys) f₁) (cmdReadWrites x sys)) ∷ mm)
 

getProperty : {mm : Memory} (x : Cmd) -> MemoryProperty mm -> (x∈ : x ∈ map proj₁ mm) -> ∃[ sys ](get x mm x∈ ≡ map (λ f₁ → f₁ , (St.run x sys) f₁) (cmdReadWrites x sys) × ∀ f₁ → f₁ ∈ cmdReadNames x sys -> sys f₁ ≡ St.run x sys f₁)
getProperty x (Cons x₁ sys ∀₁ mp) x∈ with x ≟ x₁
... | yes x≡x₁ = sys , cong (λ x₂ → map (λ f₁ → f₁ , foldr extend sys (proj₂ (proj₁ (oracle x₂) sys)) f₁) (cmdReadWrites x₂ sys)) (sym x≡x₁) , λ f₁ x₂ → subst (λ x₃ → sys f₁ ≡ St.run x₃ sys f₁) (sym x≡x₁) (∀₁ f₁ (subst (λ x₃ → f₁ ∈ map proj₁ (proj₁ (proj₁ (oracle x₃) sys))) x≡x₁ x₂))
... | no ¬x≡x₁ = getProperty x mp (tail ¬x≡x₁ x∈)

lemma1 : ∀ (s : FileSystem) {s₁} {x} ls ls₁ → All (λ (f₁ , v₁) → s f₁ ≡ v₁) ls → ls ≡ map (λ f₁ → f₁ , (St.run x s₁) f₁) ls₁ → All (λ f₁ → s f₁ ≡ St.run x s₁ f₁) ls₁
lemma1 s [] [] all₁ ≡₁ = All.[]
lemma1 s (x₁ ∷ ls) (x ∷ ls₁) (px All.∷ all₁) ≡₁ with ∷-injective ≡₁
... | x₁≡x , ≡₂ = (trans (subst (λ x₂ → s x₂ ≡ proj₂ x₁) (,-injectiveˡ x₁≡x) px) (,-injectiveʳ x₁≡x)) All.∷ (lemma1 s ls ls₁ all₁ ≡₂)

{- Want to prove that system will be the same whether or not we run the command; -}
{- If a command's inputs and outputs are unchanged from when it was last run,
 then running it will have no effect. -}
noEffect : ∀ {s₁} {s₂ : FileSystem} {mm} x → (∀ f₁ → s₁ f₁ ≡ s₂ f₁) → MemoryProperty mm → (x∈ : x ∈ map proj₁ mm) → All (λ (f₁ , v₁) → s₂ f₁ ≡ v₁) (get x mm x∈) → ∀ f₁ → s₂ f₁ ≡ St.run x s₁ f₁
noEffect {s₁} {s₂} {mm} x ∀₁ mp x∈ all₁ f₁ with getProperty x mp x∈
... | s₃ , get≡ , ∀₂ with f₁ ∈? cmdWriteNames x s₁
... | no f₁∉ = trans (sym (∀₁ f₁)) (lemma3 f₁ (proj₂ (proj₁ (oracle x) s₁)) f₁∉)
... | yes f₁∈ with lemma1 s₂ (get x mm x∈) (cmdReadWrites x s₃) all₁ get≡
... | all₂ with proj₂ (oracle x) s₃ s₁ (λ f₂ x₁ → sym (trans (∀₁ f₂) (trans (lookup all₂ (∈-++⁺ˡ x₁)) (sym (∀₂ f₂ x₁)))))
... | ≡₁ = trans (lookup all₂ (∈-++⁺ʳ (cmdReadNames x s₃) f₁∈₁))
                 (subst (λ x₁ → foldr extend s₃ x₁ f₁ ≡ foldr extend s₁ (proj₂ (proj₁ (oracle x) s₁)) f₁)
                        (sym (cong proj₂ ≡₁))
                        (lemma4 (proj₂ (proj₁ (oracle x) s₁)) f₁ f₁∈))
  where f₁∈₁ : f₁ ∈ cmdWriteNames x s₃
        f₁∈₁ = subst (λ ls → f₁ ∈ ls) (sym (cong (map proj₁ ∘ proj₂) ≡₁)) f₁∈


doRunSoundness : ∀ st ls {st₁} {ls₁} b x → doRunWError {b} (st , ls) x ≡ inj₂ (st₁ , ls₁) → doRun st x ≡ st₁
doRunSoundness st ls b x ≡₁ with checkHazard (proj₁ st) x {b} ls
... | nothing = cong proj₁ (inj₂-injective ≡₁)

runSoundness : ∀ s m ls st₁ ls₁ b x → runWError {b} x s m ls ≡ inj₂ (st₁ , ls₁) → runR x (s , m) ≡ st₁
runSoundness s m ls st₁ ls₁ b x ≡₁ with run? x (s , m)
... | false = cong proj₁ (inj₂-injective ≡₁)
... | true = doRunSoundness (s , m) ls b x ≡₁
\end{code}

\begin{code}[hide]
soundness-inner : ∀ {st₁} {ls₁} st ls b₁ b₂ → rattle b₁ b₂ (st , ls) ≡ inj₂ (st₁ , ls₁) → rattle_unchecked b₁ st ≡ st₁
soundness-inner st ls [] b₂ ≡₁ = cong proj₁ (inj₂-injective ≡₁)
soundness-inner (s , m) ls (x ∷ b₁) b₂  ≡₁ with runWError {b₂} x s m ls | inspect (runWError {b₂} x s m) ls
... | inj₂ (st₂ , ls₂) | [ ≡₂ ] with runSoundness s m ls st₂ ls₂ b₂ x ≡₂
... | ≡st₂ = subst (λ x₁ → rattle_unchecked b₁ x₁ ≡ _) (sym ≡st₂) (soundness-inner st₂ ls₂ b₁ b₂ ≡₁)

OKBuild : State → FileInfo → Build → Build → Set
OKBuild (s , mm) ls b₁ b₂ = DisjointBuild s b₁ × MemoryProperty mm × UniqueEvidence b₁ b₂ (map proj₁ ls)
\end{code}

\newcommand{\soundness}{%
\begin{code}
soundness : ∀ {st} {ls} s br bc → rattle br bc ((s , []) , []) ≡ inj₂ (st , ls) → rattle_unchecked br (s , []) ≡ st 
\end{code}}
\begin{code}[hide]
soundness s br bc ≡₁ = soundness-inner (s , []) [] br bc ≡₁
\end{code}

\begin{code}[hide]
completeness-inner : ∀ st ls b₁ b₂ → OKBuild st ls b₁ b₂ → HazardFree (proj₁ st) b₁ b₂ ls
             → ∃[ st₁ ](∃[ ls₁ ](rattle b₁ b₂ (st , ls) ≡ inj₂ (st₁ , ls₁)))
completeness-inner st ls [] _ (dsb , mp , (ub₁ , ub₂ , uls , dsj)) hf = st , ls , refl
completeness-inner st@(s , mm) ls (x ∷ b₁) b₂ ((Cons .x ds .b₁ dsb) , mp , ((px ∷ ub₁) , ub₂ , uls , dsj₁))  (:: .s .ls .x .b₁ .b₂ ¬hz hf) with x ∈? map proj₁ mm
... | yes x∈ with maybeAll {s} (get x mm x∈)
... | nothing with checkHazard s x {b₂} ls
... | just hz = ⊥-elim (¬hz hz)
... | nothing = completeness-inner st₂ ls₂ b₁ b₂ (dsb , mp₂ , (ub₁ , ub₂ , uls₂ , dsj₂)) hf
  where dsj₂ : Disjoint b₁ (x ∷ map proj₁ ls)
        dsj₂ = λ x₁ → dsj₁ (there (proj₁ x₁) , tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
        st₂ : State
        st₂ = St.run x s , save x ((cmdReadNames x s) ++ (cmdWriteNames x s)) (St.run x s) mm
        ls₂ : FileInfo
        ls₂ = rec s x ls
        uls₂ : Unique (x ∷ map proj₁ ls)
        uls₂ = g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls
        mp₂ : MemoryProperty (proj₂ st₂)
        mp₂ = MemoryProperty.Cons x s (λ f₁ x₂ → lemma3 f₁ (proj₂ (proj₁ (oracle x) s)) λ x₃ → ds (x₂ , x₃)) mp

completeness-inner st@(s , mm) ls (x ∷ b₁) b₂ ((Cons .x x₁ .b₁ dsb) , mp , ((px ∷ ub₁) , ub₂ , uls , dsj₁))  (:: .s .ls .x .b₁ .b₂ ¬hz hf) | yes x∈ | just all₁ with noEffect x (λ f₁ → refl) mp x∈ all₁
... | ∀₁ = completeness-inner st ls b₁ b₂ ((dsj-≡ (St.run x s) s b₁ ∀₁ dsb) , mp , (ub₁ , ub₂ , uls , dsj₃))  hf₂
  where dsj₃ : Disjoint b₁ (map proj₁ ls)
        dsj₃ = λ x₂ → dsj₁ (there (proj₁ x₂) , proj₂ x₂)
        dsj₂ : Disjoint b₁ (x ∷ map proj₁ ls)
        dsj₂ = λ x₁ → dsj₁ (there (proj₁ x₁) , tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
        uls₂ : Unique (x ∷ map proj₁ ls)
        uls₂ = g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls
        hf₂ : HazardFree s b₁ b₂ ls
        hf₂ = hf-still b₁ [] ((x , cmdReadNames x s , cmdWriteNames x s) ∷ []) ls (λ f₁ x₂ → sym (∀₁ f₁)) ub₁ uls₂ dsj₂ hf
        
completeness-inner st@(s , mm) ls (x ∷ b₁) b₂ ((Cons .x ds .b₁ dsb) , mp , ((px ∷ ub₁) , ub₂ , uls , dsj₁))  (:: .s .ls .x .b₁ .b₂ ¬hz hf) |  no x∉ with checkHazard s x {b₂} ls
... | just hz = ⊥-elim (¬hz hz)
... | nothing = completeness-inner (St.run x s , save x ((cmdReadNames x s) ++ (cmdWriteNames x s)) (St.run x s) mm) (rec s x ls) b₁ b₂ (dsb , (MemoryProperty.Cons x s (λ f₁ x₂ → lemma3 f₁ (proj₂ (proj₁ (oracle x) s)) λ x₃ → ds (x₂ , x₃)) mp) , (ub₁ , ub₂ , (g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls) , dsj₂)) hf 
  where dsj₂ : Disjoint b₁ (x ∷ map proj₁ ls)
        dsj₂ = λ x₁ → dsj₁ (there (proj₁ x₁) , tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
\end{code}

\newcommand{\completeness}{%
\begin{code}
completeness : ∀ s br bc → PreCond s br bc → HazardFree s br bc [] → ∃[ st ](∃[ ls ](rattle br bc ((s , []) , []) ≡ inj₂ (st , ls)))
\end{code}}
\begin{code}[hide]
completeness s br bc (dsb , ubr , ubc , _) hf = completeness-inner (s , []) [] br bc (dsb , ([] , ubr , (ubc , (Data.List.Relation.Unary.AllPairs.[] , g₁)))) hf
  where g₁ : Disjoint br []
        g₁ ()
\end{code}

\begin{code}[hide]
script≡rattle-inner : ∀ {s₁} {s₂} m b₁ → (∀ f₁ → s₁ f₁ ≡ s₂ f₁) → DisjointBuild s₂ b₁ → MemoryProperty m
              → (∀ f₁ → script b₁ s₁ f₁ ≡ proj₁ (rattle_unchecked b₁ (s₂ , m)) f₁)
script≡rattle-inner mm [] ∀₁ dsb mp = ∀₁ 
script≡rattle-inner {s₁} {s₂} mm (x ∷ b₁) ∀₁ (Cons .x dsj .b₁ dsb) mp f₁ with x ∈? map proj₁ mm
... | no x∉ = script≡rattle-inner {St.run x s₁} {St.run x s₂} (save x (cmdReadNames x s₂ ++ cmdWriteNames x s₂) (St.run x s₂) mm) b₁ (run-≡ x ∀₁) dsb mp₁ f₁
  where mp₁ : MemoryProperty (save x (cmdReadNames x s₂ ++ cmdWriteNames x s₂) (St.run x s₂) mm)
        mp₁ = Cons x s₂ (λ f₂ x₁ → lemma3 f₂ (proj₂ (proj₁ (oracle x) s₂)) λ x₂ → dsj (x₁ , x₂)) mp
... | yes x∈ with maybeAll {s₂} (get x mm x∈)
... | nothing = script≡rattle-inner {St.run x s₁} {St.run x s₂} (save x (cmdReadNames x s₂ ++ cmdWriteNames x s₂) (St.run x s₂) mm) b₁ (run-≡ x ∀₁) dsb mp₁ f₁
  where mp₁ : MemoryProperty (save x (cmdReadNames x s₂ ++ cmdWriteNames x s₂) (St.run x s₂) mm)
        mp₁ = Cons x s₂ (λ f₂ x₁ → lemma3 f₂ (proj₂ (proj₁ (oracle x) s₂)) λ x₂ → dsj (x₁ , x₂)) mp
... | just all₁ = script≡rattle-inner {St.run x s₁} {s₂} mm b₁ ∀₂ (dsj-≡ (St.run x s₂) s₂ b₁ ∀₃ dsb) mp f₁
  where ∀₂ : ∀ f₁ → St.run x s₁ f₁ ≡ s₂ f₁
        ∀₂ f₁ = sym (noEffect x ∀₁ mp x∈ all₁ f₁)
        ∀₃ : ∀ f₁ → s₂ f₁ ≡ St.run x s₂ f₁
        ∀₃ = noEffect x (λ f₂ → refl) mp x∈ all₁

-- rattle produces a State and the System in that state is equivalent to the one produced by script
\end{code}

\newcommand{\eqtoscript}{%
\begin{code}
≡toScript : FileSystem → Build → Build → Set
≡toScript s br bc = ∃[ s₁ ](∃[ m ](∃[ ls ](rattle br bc ((s , []) , []) ≡ inj₂ ((s₁ , m) , ls) × ∀ f₁ → s₁ f₁ ≡ script bc s f₁)))
\end{code}}

\newcommand{\lemmasr}{%
\begin{code}
script≡rattle_unchecked : ∀ s b → DisjointBuild s b → (∀ f₁ → script b s f₁ ≡ proj₁ (rattle_unchecked b (s , [])) f₁)
\end{code}}
\begin{code}[hide]
script≡rattle_unchecked s b dsb = script≡rattle-inner [] b (λ f₁ → refl) dsb []
\end{code}

\begin{code}[hide]
-- correctness is if you have any build then either you get the right answer (the one the script gave) or you get an error and there was a hazard.
\end{code}
\newcommand{\correct}{%
\begin{code}
correct_rattle : ∀ s bc → PreCond s bc bc → ¬ HazardFree s bc bc [] ⊎ ≡toScript s bc bc
correct_rattle s bc pc with rattle bc bc ((s , []) , []) | inspect (rattle bc bc) ((s , []) , [])
... | inj₁ hz | [ ≡₁ ] = inj₁ g₁
  where g₁ : ¬ HazardFree s bc bc []
        g₁ hf with completeness s bc bc pc hf
        ... | a , fst , ≡₂ = contradiction (trans (sym ≡₁) ≡₂) λ ()
... | inj₂ ((s₁ , mm₁) , ls₁) | [ ≡₁ ] = inj₂ (s₁ , mm₁ , ls₁ , refl , ∀≡)
  where ∀≡ : ∀ f₁ → s₁ f₁ ≡ script bc s f₁
        ∀≡ f₁ = sym (trans (script≡rattle_unchecked s bc (proj₁ pc) f₁)
                           (cong-app (cong proj₁ (soundness s bc bc ≡₁)) f₁))
\end{code}}


\begin{code}[hide]
-- want to prove if execWError original build produces a hazard then execWError of the reordered build will produce a hazard too.
-- this would also mean if the reordered build doesnt produce a hazard, then the original build doesn't produce a hazard.
-- which means it produces a state.
-- then we use soundness to prove theyre equal to their non hazard versions ; then we use the reordering proof to show they're equivalent??

extra-lemma : ∀ s x y b₁ b₂ ls → x ∈ b₂ → y ∈ b₂ → ¬ HazardFree s b₂ b₁ ls
extra-lemma s x y b₁ (x₁ ∷ b₂) ls x∈b₁ y∈b₁ (:: .s .ls .x₁ .b₂ .b₁ ¬hz hf) = {!!}

-- for every pair of commands in b₂ (x , y) where x is before y; if x writes to something y reads; then (x , y) in b₁ too.

preservesHazards : ∀ s ls b₁ b₂ → b₁ ⊆ b₂ → Unique b₁ → Unique b₂ → ¬ HazardFree s b₁ [] ls → ¬ HazardFree s b₂ b₁ ls
preservesHazards s ls b₁ b₂ ⊆₁ ue ue₁ ¬hf hf = ¬hf {!!}
  where --g₃ : ∀ {v} → v ∈ cmdWriteNames x s → v ∈ files ls₂ → ⊥
  
        g₁ : ∀ s b₁ b₂ ls₁ ls₂ → HazardFree s b₂ b₁ ls₁ → HazardFree s b₁ [] ls₂
        g₁ s b₁ [] ls₁ ls₂ hf = {!!}
        g₁ s b₁ (x ∷ b₂) ls₁ ls₂ hf = {!!}

{- if you have a pair of commands in b₂. (x , y) either or speculative hazard in b₂
 
-}

{- we know:
  x is in b₂ ; 
  x ∈ b₁ ; 
  x wrote to something a command in ls₂ read.   ; we should know ls₁ is a subset of ls₂
  if the command in ls₂ is in ls₁ 

  if there is a read/write or write/write hazard. => either there is a read/write write/write hazard or a speculative hazard.
 


-}

-- :: s ls x b₁ [] (λ _ _ _ ∈[] _ _ → contradiction ∈[] (λ ())) (λ x₂ → contradiction ({!!} , {!!}) (¬sh {!!} {!!} {!!} {!!} {!!})) {!!}

{- preserving hazards:  Need to prove if the reordered build is hazardfree; then the original build is hazardfree.  

we know: there is a hazard there; read/write or write/write. we know x writes to something that
the build previously wrote.  somehow we need to produce a contradiction. 

we would have a speculative hazard if 

-}

\end{code}

\begin{code}[hide]
correct2 : ∀ br bc s m ls → OKBuild (s , m) ls br bc → bc ↭ br → ¬ HazardFree s bc bc ls ⊎ ∃[ s₁ ](∃[ m₁ ](∃[ ls₁ ](rattle br bc ((s , m) , ls) ≡ inj₂ ((s₁ , m₁) , ls₁) × ∀ f₁ → s₁ f₁ ≡ script bc s f₁)))
correct2 b₁ b₂ s mm ls (dsb , mp , ue) p with rattle b₁ b₂ ((s , mm) , ls) | inspect (rattle b₁ b₂) ((s , mm) , ls)
... | inj₁ hz | [ ≡₁ ] = {!!}
{- proof plan:
  we know the reorderd build produced a hazard. this doesnt mean the original build has a hazard.  
  we could prove this case if we know the incorrect build doesn't corrupt the "inputs" of the build. 
  then we can run the correct build sequentially... and we would show that all the outputs of the build are still correct; so
  this says the systems are not exactly equivalent, but are equivalent for the outputs the build was MEANT to write.  
  for us to do both of these cases; we should change this lemma to say it only produces the same outputs for a certain set of files
-}
... | inj₂ (st , _) | [ ≡₁ ] = {!!} -- inj₂ ((st , _) , refl , λ f₁ → sym (trans {!!} {!!}))

{-soundness : execwError b₁ = exec b₁ = script.exec b₁
                            exec b₂ = script.exec b₂ -}

{- proof plan: 
  we know the reordered build doesn't produce a hazard.  which via some math should mean the original build doesnt produce a hazard. 
  1. get evidnce running the original build returns inj₂ 
  2. apply soundness to both.  
  3. use reordering proof. to show theyre the same for all files??  Of course we can only show that for two builds which are permutations where there are no extra commands.
     if we want to support the extra command thing the reodering proof needs to be expanded.
-}


{- maybe in the paper we could just prove this for the case where speculation doesnt cause hazards. and explain future work proving the other case?
  so prove a subset of the correct2 lemma?
-}
\end{code}

\newcommand{\correctS}{%
\begin{code}
correct_speculation : ∀ s br bc → PreCond s br bc → ¬ HazardFree s bc bc [] ⊎ ≡toScript s br bc
\end{code}}
\begin{code}[hide]
correct_speculation s br bc pc = {!!}
\end{code}

\begin{code}[hide]
semi-correct : ∀ s m ls b₁ b₂ → DisjointBuild s b₁ → MemoryProperty m → UniqueEvidence b₁ b₂ (map proj₁ ls) → b₂ ↭ b₁ → ¬ HazardFree s b₁ b₂ ls ⊎ ¬ HazardFree s b₂ b₂ ls ⊎ ∃[ s₁ ](∃[ m₁ ](∃[ ls₁ ](rattle b₁ b₂ ((s , m) , ls) ≡ inj₂ ((s₁ , m₁) , ls₁) × ∀ f₁ → s₁ f₁ ≡ script b₂ s f₁)))
             -- ≡toScript (s , m) ls b₁ b₂ b₂
semi-correct s mm ls b₁ b₂ dsb mp ue b₂↭b₁ with hazardfree? s b₁ b₂ ls
... | no hz = inj₁ hz
... | yes hf with hazardfree? s b₂ b₂ ls
... | no hz = inj₂ (inj₁ hz)
... | yes hf₁ with completeness-inner (s , mm) ls b₁ b₂ (dsb , mp , ue) hf
... | (s₁ , mm₁) , ls₁ , ≡₁ = inj₂ (inj₂ (s₁ , mm₁ , ls₁ , ≡₁ , λ f₁ → sym (trans (reordered b₂ b₁ ls b₂↭b₁ ue {!!} hf f₁) (trans (script≡rattle-inner mm b₁ (λ f₂ → refl) dsb mp f₁) (cong-app (cong proj₁ (soundness-inner (s , mm) ls b₁ b₂ ≡₁)) f₁)))))
-- 
\end{code}


\newcommand{\correctP}{%
\begin{code}
semi_correct : ∀ s br bc → PreCond s br bc → ¬ HazardFree s br bc [] ⊎ ¬ HazardFree s bc bc [] ⊎ ≡toScript s br bc
semi_correct s br bc pc with hazardfree? s br bc []
... | no hz = inj₁ hz
... | yes hf₁ with hazardfree? s bc bc []
... | no hz = inj₂ (inj₁ hz)
... | yes hf₂ with completeness s br bc pc hf₁
... | (s₁ , m₁) , ls , ≡₁ = inj₂ (inj₂ (s₁ , m₁ , ls , ≡₁ , ∀≡))
  where ∀≡ : ∀ f₁ → s₁ f₁ ≡ script bc s f₁
        ∀≡ f₁ = sym (trans (reordered≡ s br bc pc hf₁ hf₂ f₁)
                           (trans (script≡rattle_unchecked s br (proj₁ pc) f₁)
                                  (cong-app (cong proj₁ (soundness s br bc ≡₁)) f₁)))
\end{code}}


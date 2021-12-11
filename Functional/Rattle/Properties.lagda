\begin{code}[hide]
open import Functional.State using (Oracle ; FileSystem ; Memory ; Cmd ; extend ; State ; save ; reads)

module Functional.Rattle.Properties (oracle : Oracle) where

open import Agda.Builtin.Equality

open import Functional.State.Helpers (oracle) as St using (cmdReadNames ; cmdWriteNames ; cmdWrites)
open import Functional.State.Properties (oracle) using (lemma3 ; lemma4 ; run-≡)
open import Common.List.Properties using (∈-resp-≡ ; l11 ; _before_∈_ ; l4 ; concatMap-++-commute)
open import Functional.Forward.Properties (oracle) using (cmdReadWrites ; IdempotentState ; IdempotentCmd ; cmdIdempotent)
open import Functional.Forward.Exec (oracle) using (get ; maybeAll ; run?)
open import Functional.File using (FileName ; FileContent)
open import Data.Bool using (true ; false ; if_then_else_)

open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∃-syntax)
open import Data.Product.Properties using (,-injectiveʳ ; ,-injectiveˡ)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Data.List using (List ; map ; _++_ ; foldr ; _∷_ ; [] ; concatMap ; reverse ; _∷ʳ_ ; length)
open import Data.List.Properties using (∷-injective ; unfold-reverse ; ++-assoc ; reverse-++-commute ; reverse-involutive ; ∷-injectiveˡ ; ∷-injectiveʳ)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Relation.Binary.PropositionalEquality using (trans ; cong ; cong-app ; sym ; decSetoid ; cong₂ ; subst ; subst₂ ; inspect ; [_])
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-++⁻ ; ∈-concat⁻ ; ∈-∃++)
open import Function.Base using (_∘_)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Data.List.Relation.Unary.Any.Properties using (reverse⁺ ; reverse⁻)
open import Functional.Rattle.Exec (oracle) using (rattle ; runWError ; runR ; doRunR ; rattle-unchecked ; doRunWError ; checkHazard ; g₂)
open import Functional.Build (oracle) using (Build ; UniqueEvidence ; PreCond ; DisjointBuild ; Cons)
open import Data.Sum using (inj₂ ; from-inj₂ ; inj₁ ; _⊎_)
open import Data.Sum.Properties using (inj₂-injective)
open import Functional.Script.Exec (oracle) as Script
open import Functional.Script.Properties (oracle) using (dsj-≡ ; exec-≡f₁ ; writes≡ ; exec-∷≡ ; exec≡₃) 
open import Functional.Script.Proofs (oracle) using (reordered ; reordered≡ ; unique-reverse ; unique-drop-mid ; helper3 ; helper5)

open import Functional.Script.Hazard (oracle) using (Hazard ; HazardFree ; FileInfo ; _∷_ ; ∃Hazard ; [] ; hazardfree? ; ReadWrite ; WriteWrite ; Speculative ; filesRead ; filesWrote ; files ; cmdsRun ; cmdWrote ; ∈-cmdWrote∷ ; ∈-cmdRead∷l ; ∈-filesWrote) renaming (save to rec)

open import Functional.Script.Hazard.Properties (oracle) using (hf-still ; hf=>disjointWR ; hf=>disjointRW ; hf=>disjointWW ; hf-drop-mid)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_ ; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭ ; ↭-length ; drop-mid)



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


doRunSoundness : ∀ st ls {st₁} {ls₁} b x → doRunWError {b} (st , ls) x ≡ inj₂ (st₁ , ls₁) → doRunR st x ≡ st₁
doRunSoundness st ls b x ≡₁ with checkHazard (proj₁ st) x {b} ls
... | nothing = cong proj₁ (inj₂-injective ≡₁)

runSoundness : ∀ s m ls st₁ ls₁ b x → runWError {b} x s m ls ≡ inj₂ (st₁ , ls₁) → runR x (s , m) ≡ st₁
runSoundness s m ls st₁ ls₁ b x ≡₁ with run? x (s , m)
... | false = cong proj₁ (inj₂-injective ≡₁)
... | true with checkHazard s x {b} ls
... | nothing = cong proj₁ (inj₂-injective ≡₁)
-- doRunSoundness (s , m) ls b x ≡₁
\end{code}

\begin{code}[hide]
soundness-inner : ∀ {st₁} {ls₁} st ls b₁ b₂ → rattle b₁ b₂ (st , ls) ≡ inj₂ (st₁ , ls₁) → rattle-unchecked b₁ st ≡ st₁
soundness-inner st ls [] b₂ ≡₁ = cong proj₁ (inj₂-injective ≡₁)
soundness-inner (s , m) ls (x ∷ b₁) b₂  ≡₁ with runWError {b₂} x s m ls | inspect (runWError {b₂} x s m) ls
... | inj₂ (st₂ , ls₂) | [ ≡₂ ] with runSoundness s m ls st₂ ls₂ b₂ x ≡₂
... | ≡st₂ = subst (λ x₁ → rattle-unchecked b₁ x₁ ≡ _) (sym ≡st₂) (soundness-inner st₂ ls₂ b₁ b₂ ≡₁)

OKBuild : State → FileInfo → Build → Build → Set
OKBuild (s , mm) ls b₁ b₂ = DisjointBuild s b₁ × MemoryProperty mm × UniqueEvidence b₁ b₂ (map proj₁ ls)
\end{code}

\begin{code}[hide]
completeness-inner : ∀ st ls b₁ b₂ → OKBuild st ls b₁ b₂ → HazardFree (proj₁ st) b₁ b₂ ls
             → ∃[ st₁ ](∃[ ls₁ ](rattle b₁ b₂ (st , ls) ≡ inj₂ (st₁ , ls₁)))
completeness-inner st ls [] _ (dsb , mp , (ub₁ , ub₂ , uls , dsj)) hf = st , ls , refl
completeness-inner st@(s , mm) ls (x ∷ b₁) b₂ ((Cons .x ds .b₁ dsb) , mp , ((px ∷ ub₁) , ub₂ , uls , dsj₁))  (¬hz ∷ hf) with x ∈? map proj₁ mm
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

completeness-inner st@(s , mm) ls (x ∷ b₁) b₂ ((Cons .x x₁ .b₁ dsb) , mp , ((px ∷ ub₁) , ub₂ , uls , dsj₁))  (¬hz ∷ hf) | yes x∈ | just all₁ with noEffect x (λ f₁ → refl) mp x∈ all₁
... | ∀₁ = completeness-inner st ls b₁ b₂ ((dsj-≡ (St.run x s) s b₁ ∀₁ dsb) , mp , (ub₁ , ub₂ , uls , dsj₃))  hf₂
  where dsj₃ : Disjoint b₁ (map proj₁ ls)
        dsj₃ = λ x₂ → dsj₁ (there (proj₁ x₂) , proj₂ x₂)
        dsj₂ : Disjoint b₁ (x ∷ map proj₁ ls)
        dsj₂ = λ x₁ → dsj₁ (there (proj₁ x₁) , tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
        uls₂ : Unique (x ∷ map proj₁ ls)
        uls₂ = g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls
        hf₂ : HazardFree s b₁ b₂ ls
        hf₂ = hf-still b₁ [] ((x , cmdReadNames x s , cmdWriteNames x s) ∷ []) ls (λ f₁ x₂ → sym (∀₁ f₁)) ub₁ uls₂ dsj₂ hf
        
completeness-inner st@(s , mm) ls (x ∷ b₁) b₂ ((Cons .x ds .b₁ dsb) , mp , ((px ∷ ub₁) , ub₂ , uls , dsj₁))  (¬hz ∷ hf) |  no x∉ with checkHazard s x {b₂} ls
... | just hz = ⊥-elim (¬hz hz)
... | nothing = completeness-inner (St.run x s , save x ((cmdReadNames x s) ++ (cmdWriteNames x s)) (St.run x s) mm) (rec s x ls) b₁ b₂ (dsb , (MemoryProperty.Cons x s (λ f₁ x₂ → lemma3 f₁ (proj₂ (proj₁ (oracle x) s)) λ x₃ → ds (x₂ , x₃)) mp) , (ub₁ , ub₂ , (g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls) , dsj₂)) hf 
  where dsj₂ : Disjoint b₁ (x ∷ map proj₁ ls)
        dsj₂ = λ x₁ → dsj₁ (there (proj₁ x₁) , tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
\end{code}

\newcommand{\completeness}{%
\begin{code}
completeness : ∀ s br bs → PreCond s br bs → HazardFree s br bs [] → ∃[ st ](∃[ ls ](rattle br bs ((s , []) , []) ≡ inj₂ (st , ls)))
\end{code}}
\begin{code}[hide]
completeness s br bc (dsb , ubr , ubc , _) hf = completeness-inner (s , []) [] br bc (dsb , ([] , ubr , (ubc , (Data.List.Relation.Unary.AllPairs.[] , g₁)))) hf
  where g₁ : Disjoint br []
        g₁ ()
\end{code}

\begin{code}[hide]
script≡rattle-inner : ∀ {s₁} {s₂} m b₁ → (∀ f₁ → s₁ f₁ ≡ s₂ f₁) → DisjointBuild s₂ b₁ → MemoryProperty m
              → (∀ f₁ → script b₁ s₁ f₁ ≡ proj₁ (rattle-unchecked b₁ (s₂ , m)) f₁)
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
≡toScript s br bs = ∃[ s₁ ](∃[ m ](∃[ ls ](rattle br bs ((s , []) , []) ≡ inj₂ ((s₁ , m) , ls) × ∀ f₁ → s₁ f₁ ≡ script bs s f₁)))
\end{code}}

\newcommand{\lemmasr}{%
\begin{code}
script≡rattle-unchecked : ∀ s b → DisjointBuild s b → (∀ f₁ → script b s f₁ ≡ proj₁ (rattle-unchecked b (s , [])) f₁)
\end{code}}
\begin{code}[hide]
script≡rattle-unchecked s b dsb = script≡rattle-inner [] b (λ f₁ → refl) dsb []
\end{code}

\newcommand{\soundness}{%
\begin{code}
soundness : ∀ {s₁} {m₁} {ls} s br bs → DisjointBuild s br → rattle br bs ((s , []) , []) ≡ inj₂ ((s₁ , m₁) , ls)
          → (∀ f₁ → script br s f₁ ≡ s₁ f₁)
\end{code}}
\begin{code}[hide]
soundness s br bc dsb ≡₁ f₁ = trans (script≡rattle-unchecked s br dsb f₁)
                                    (cong-app (,-injectiveˡ (soundness-inner (s , []) [] br bc ≡₁)) f₁)
\end{code}

\begin{code}[hide]
-- correctness is if you have any build then either you get the right answer (the one the script gave) or you get an error and there was a hazard.
\end{code}
\newcommand{\correct}{%
\begin{code}
correct-rattle : ∀ s b → PreCond s b b → ¬ HazardFree s b b [] ⊎ ≡toScript s b b
\end{code}}
\begin{code}[hide]
correct-rattle s b pc with rattle b b ((s , []) , []) | inspect (rattle b b) ((s , []) , [])
... | inj₁ hz | [ ≡₁ ] = inj₁ g₁
  where g₁ : ¬ HazardFree s b b []
        g₁ hf with completeness s b b pc hf
        ... | a , fst , ≡₂ = contradiction (trans (sym ≡₁) ≡₂) λ ()
... | inj₂ ((s₁ , mm₁) , ls₁) | [ ≡₁ ] = inj₂ (s₁ , mm₁ , ls₁ , refl , ∀≡)
  where ∀≡ : ∀ f₁ → s₁ f₁ ≡ script b s f₁
        ∀≡ f₁ = sym (soundness s b b (proj₁ pc) ≡₁ f₁)
\end{code}


\begin{code}[hide]
-- want to prove if execWError original build produces a hazard then execWError of the reordered build will produce a hazard too.
-- this would also mean if the reordered build doesnt produce a hazard, then the original build doesn't produce a hazard.
-- which means it produces a state.
-- then we use soundness to prove theyre equal to their non hazard versions ; then we use the reordering proof to show they're equivalent??

-- for every pair of commands in b₂ (x , y) where x is before y; if x writes to something y reads; then (x , y) in b₁ too.

before=>∈ : ∀ {x₁} {x₂} {xs} → x₁ before x₂ ∈ xs → (x₁ ∈ xs × x₂ ∈ xs)
before=>∈ (ys , zs , ≡₁ , x₂∈zs) = (subst (λ x → _ ∈ x) (sym ≡₁) (∈-++⁺ʳ ys (here refl)))
                                   , (subst (λ x → _ ∈ x) (sym ≡₁) (∈-++⁺ʳ ys (there x₂∈zs)))

still-hazard : ∀ {s} {ls} x₁ x b → ¬ x₁ ≡ x → x ∉ (map proj₁ ls) → Hazard s x₁ (b ++ x ∷ []) ls → Hazard s x₁ b ls
still-hazard x₁ x b _ x∉ls (ReadWrite x₂ x₃) = (ReadWrite x₂ x₃)
still-hazard x₁ x b _ x∉ls (WriteWrite x₂ x₃) = (WriteWrite x₂ x₃)
still-hazard x₁ x b ¬x₁≡x x∉ls (Speculative x₂ x₃ x₄ x₅ x₆ x₇ x₈)
  = Speculative x₂ x₃ x₄ x₃∈b ¬bf x₇ x₈
    where x₃∈b : x₃ ∈ b
          x₃∈b with ∈-++⁻ b x₅
          ... | inj₁ x₃∈₁ = x₃∈₁
          ... | inj₂ (here px₁) with before=>∈ x₄
          ... | here px , ∈₂ = contradiction (sym (trans (sym px₁) px)) ¬x₁≡x
          ... | there ∈₁ , ∈₂ = contradiction (subst (λ x₉ → x₉ ∈ _) px₁ ∈₁) x∉ls
          ¬bf : ¬ (x₂ before x₃ ∈ b)
          ¬bf (xs , ys , ≡₁ , ∈₁) = x₆ (xs , ys ++ x ∷ [] , trans (cong (_++ x ∷ []) ≡₁) (++-assoc xs (x₂ ∷ ys) (x ∷ [])) , ∈-++⁺ˡ ∈₁)

script-rec : ∀ (b : Build) s ls → FileInfo
script-rec [] s ls = ls
script-rec (x ∷ b) s ls = script-rec b (St.run x s) (rec s x ls)

script-rec-++ : ∀ {s} {as} {bs} xs → script-rec xs s (as ++ bs) ≡ script-rec xs s as ++ bs
script-rec-++ [] = refl
script-rec-++ (x ∷ xs) = script-rec-++ xs

before-reverse : ∀ x₁ x₂ (xs : Build) → x₁ before x₂ ∈ xs → x₂ before x₁ ∈ (reverse xs)
before-reverse x₁ x₂ xs (ys , zs , ≡₁ , x₂∈zs) with ∈-∃++ x₂∈zs
... | (as , bs , ≡₂) = reverse bs , reverse (ys ++ x₁ ∷ as) , ≡₃ , reverse⁺ (∈-++⁺ʳ ys (here refl))
  where ≡₃ : reverse xs ≡ reverse bs ++ x₂ ∷ reverse (ys ++ x₁ ∷ as)
        ≡₃ with trans (subst (λ x → xs ≡ ys ++ x₁ ∷ x) ≡₂ ≡₁) (sym (++-assoc ys (x₁ ∷ as) (x₂ ∷ bs)))
        ... | a = trans (cong reverse a)
                        (trans (reverse-++-commute (ys ++ x₁ ∷ as) (x₂ ∷ bs))
                               (trans (cong (_++ reverse (ys ++ x₁ ∷ as)) (unfold-reverse x₂ bs))
                                      (l4 x₂ (reverse bs))))


preserves-++ : ∀ {s} {ls} x b₁ b₂ → (cmdsRun (script-rec b₁ s ls)) ≡ reverse b₂ → Disjoint (files (script-rec b₁ s ls)) (cmdWriteNames x (script b₁ s)) → x ∉ (map proj₁ ls) → x ∉ b₁ → HazardFree s b₁ b₂ ls → HazardFree s (b₁ ++ x ∷ []) (b₂ ++ x ∷ []) ls
preserves-++ x [] b₂ ≡₁ dsj _ _ [] = g₁ ∷ []
  where g₁ : ¬ Hazard _ x (b₂ ++ x ∷ []) _
        g₁ (ReadWrite x x₁) = dsj (∈-++⁺ˡ x₁ , x)
        g₁ (WriteWrite x x₁) = dsj (∈-++⁺ʳ _ x₁ , x)
        g₁ (Speculative x₁ x₂ y x₃ x₄ x₅ x₆) with before-reverse x₂ x₁ (x ∷ reverse b₂) (subst (λ x₇ → x₂ before x₁ ∈ x₇) (cong (x ∷_) ≡₁) y)
        ... | bf = x₄ (subst (λ x₁₀ → x₁ before x₂ ∈ x₁₀) (trans (unfold-reverse x (reverse b₂)) (cong (_++ x ∷ []) (reverse-involutive b₂))) bf)
preserves-++ {s} {ls} x (x₁ ∷ b₁) b₂ ≡₁ dsj x∉ls x∉b₁ (x₂ ∷ hf) = (g₁ x∉ls x₂) ∷ (preserves-++ x b₁ b₂ ≡₁ dsj x∉₁ (λ x₃ → x∉b₁ (there x₃)) hf)
  where g₁ : ∀ {s} {ls} → x ∉ (map proj₁ ls) → ¬ Hazard s x₁ b₂ ls → ¬ Hazard s x₁ (b₂ ++ x ∷ []) ls
        g₁ x∉ls ¬hz hz = ¬hz (still-hazard _ x b₂ (λ x₄ → x∉b₁ (here (sym x₄))) x∉ls hz)
        x∉₁ : x ∉ x₁ ∷ map proj₁ ls
        x∉₁ (here px) = x∉b₁ (here px)
        x∉₁ (there x∈ls) = x∉ls x∈ls


add-back-read : ∀ {s} {ls} as bs xs x → filesRead (script-rec xs s ls) ⊆ filesRead (script-rec (as ++ bs) s ls)
              → filesRead (script-rec (xs ++ x ∷ []) s ls) ⊆ filesRead (script-rec (as ++ x ∷ bs) s ls)
add-back-read {s} {ls} as bs xs x ⊆₁ x₂ with ∈-++⁻ (filesRead (script-rec xs s ls)) {!!}
{- proves filesRead (script-rec (xs ++ x ∷ []) s ls ≡ filesRead script-rec xs ++ cmdwriteNames x -}
... | inj₁ ∈₁ with ⊆₁ ∈₁
... | a = {!!}
{- prove (filesRead (script-rec (as ++ bs) s ls subset of (filesRead (script-rec (as ++ x ∷ bs) s ls
-}
add-back-read {s} {ls} xs as bs x ⊆₁ x₂ | inj₂ ∈₁ = {!!}
{- prove (cmdWriteNames x (script xs s)) subset of filesRead (script-rec (as ++ x ∷ bs))... -}


filesRead-sub :  ∀ {s} {ls} xs ys → length xs ≡ length ys → xs ↭ ys → HazardFree s xs (reverse ys) ls → filesRead (script-rec (reverse ys) s ls) ⊆ filesRead (script-rec xs s ls)
filesRead-sub [] [] _ p hf = λ x₂ → x₂
filesRead-sub {s} xs (x ∷ ys) _ p hf with ∈-∃++ (∈-resp-↭ (↭-sym p) (here refl))
... | (as , bs , ≡₁) with add-back-read as bs (reverse ys) x (filesRead-sub (as ++ bs) ys (↭-length ↭₂) ↭₂ hf₁)
  where ↭₂ : as ++ bs ↭ ys
        ↭₂ = drop-mid as [] (subst (λ x₁ → x₁ ↭ x ∷ ys) ≡₁ p)
        hf₀ : HazardFree s (as ++ x ∷ bs) ((reverse ys) ++ x ∷ []) _
        hf₀ = subst₂ (λ x₂ x₃ → HazardFree s x₂ x₃ _) ≡₁ (unfold-reverse x ys) hf
        hf₁ : HazardFree s (as ++ bs) (reverse ys) _
        hf₁ = hf-drop-mid as bs (reverse ys) {!!} -- (λ x₂ → ∈-resp-↭ (subst₂ (λ x₀ x₁ → x₀ ↭ x₁) ≡₁ (unfold-reverse x (reverse ys)) p) x₂)
                          {!!} {!!} {!!} {!!} hf₀
... | a = subst₂ (λ x₂ x₃ → filesRead (script-rec x₂ s _) ⊆ filesRead (script-rec x₃ s _)) (sym (unfold-reverse x ys)) (sym ≡₁) a


extra-lemma3-reads : ∀ {s} {ls} bs xs x → x ∉ bs → x ∉ xs → bs ⊆ xs → HazardFree s bs (xs ++ x ∷ []) ls → Disjoint (filesRead (script-rec bs s [])) (cmdWrote ls x)
extra-lemma3-reads {s} {ls} (x₁ ∷ bs) xs x x∉bs x∉xs bs⊆xs (¬hz ∷ hf) (fst , v∈ls) with ∈-++⁻ (filesRead (script-rec bs (St.run x₁ s) [])) (subst (λ x₂ → _ ∈ x₂) ≡₁ fst)
  where ≡₁ : filesRead (script-rec bs (St.run x₁ s) (rec s x₁ [])) ≡ filesRead (script-rec bs (St.run x₁ s) []) ++ (filesRead (rec s x₁ []))
        ≡₁ = trans (cong filesRead (script-rec-++ bs)) (concatMap-++-commute (proj₁ ∘ proj₂) (script-rec bs (St.run x₁ s) []) (rec s x₁ []))
... | inj₁ ∈₁ = (extra-lemma3-reads bs xs x (λ x₂ → x∉bs (there x₂)) x∉xs (λ x₂ → bs⊆xs (there x₂)) hf) (∈₁ , ∈-cmdWrote∷ (x₁ , _ , _) x ls v∈ls λ x₁≡x → x∉bs (here (sym x₁≡x)))
... | inj₂ ∈₁ = ¬hz (Speculative x x₁ bf (∈-++⁺ˡ (bs⊆xs (here refl))) (¬bf xs (bs⊆xs (here refl)) x∉xs) (∈-cmdRead∷l (x₁ , _ , _) ls (∈₂ ∈₁)) (∈-cmdWrote∷ (x₁ , _ , _) x ls v∈ls λ x₁≡x → x∉bs (here (sym x₁≡x))))
  where ∈₂ : ∀ {v} → v ∈ cmdReadNames x₁ s ++ [] → v ∈ cmdReadNames x₁ s
        ∈₂ v∈ with ∈-++⁻ (cmdReadNames x₁ s) v∈
        ... | inj₁ v∈₁ = v∈₁
        ... | inj₂ ()
        bf : x₁ before x ∈ (x₁ ∷ cmdsRun ls)
        bf = [] , cmdsRun ls , refl , {!!}
        ¬bf : ∀ xs → x₁ ∈ xs → x ∉ xs → ¬ (x before x₁ ∈ (xs ++ x ∷ []))
        ¬bf (x₂ ∷ xs) _  x∉x₂∷xs ([] , zs , ≡₁ , ∈₁) = contradiction (here (sym (∷-injectiveˡ ≡₁))) x∉x₂∷xs
        ¬bf (x₃ ∷ xs) x₁∈xs x∉xs (x₂ ∷ ys , zs , ≡₁ , ∈₁) = ¬bf xs (tail {!!} x₁∈xs) (λ x₄ → x∉xs (there x₄)) {!!}


extra-lemma3-writes : ∀ {s} {ls} bs xs x → x ∉ bs → x ∉ xs → bs ⊆ xs → HazardFree s bs (xs ++ x ∷ []) ls → Disjoint (filesWrote (script-rec bs s [])) (cmdWrote ls x)
extra-lemma3-writes {s} {ls} (x₁ ∷ bs) xs x x∉bs x∉xs bs⊆xs (¬hz ∷ hf) (fst , v∈ls) with ∈-++⁻ (filesWrote (script-rec bs (St.run x₁ s) [])) (subst (λ x₂ → _ ∈ x₂) ≡₁ fst)
  where ≡₁ : filesWrote (script-rec bs (St.run x₁ s) (rec s x₁ [])) ≡ filesWrote (script-rec bs (St.run x₁ s) []) ++ (filesWrote (rec s x₁ []))
        ≡₁ = trans (cong filesWrote (script-rec-++ bs)) (concatMap-++-commute (proj₂ ∘ proj₂) (script-rec bs (St.run x₁ s) []) (rec s x₁ []))
... | inj₁ ∈₁ = (extra-lemma3-writes bs xs x (λ x₂ → x∉bs (there x₂)) x∉xs (λ x₂ → bs⊆xs (there x₂)) hf)
                (∈₁ , ∈-cmdWrote∷ (x₁ , _ , _) x ls v∈ls λ x₁≡x → x∉bs (here (sym x₁≡x)))
... | inj₂ ∈₁ = ¬hz (WriteWrite (∈₂ ∈₁) (∈-filesWrote ls v∈ls))
  where ∈₂ : ∀ {v} → v ∈ cmdWriteNames x₁ s ++ [] → v ∈ cmdWriteNames x₁ s
        ∈₂ v∈ with ∈-++⁻ (cmdWriteNames x₁ s) v∈
        ... | inj₁ v∈₁ = v∈₁
        ... | inj₂ ()


extra-lemma3 : ∀ {s} {ls} bs xs x → x ∉ bs → x ∉ xs → bs ⊆ xs → HazardFree s bs (xs ++ x ∷ []) ls → Disjoint (files (script-rec bs s [])) (cmdWrote ls x)
extra-lemma3 {s} bs xs x x∉bs x∉xs bs⊆xs hf x₂ with ∈-++⁻ (filesRead (script-rec bs s [])) (proj₁ x₂)
... | inj₁ ∈₁ = contradiction (∈₁ , (proj₂ x₂)) (extra-lemma3-reads bs xs x x∉bs x∉xs bs⊆xs hf)
... | inj₂ ∈₁ = contradiction (∈₁ , (proj₂ x₂)) (extra-lemma3-writes bs xs x x∉bs x∉xs bs⊆xs hf)


extra-lemma : ∀ {s} {ls} as bs xs x → HazardFree s (as ++ x ∷ bs) (xs ++ x ∷ []) ls → Disjoint (files (script-rec as s ls)) (cmdWriteNames x (script as s)) × Disjoint (files (script-rec bs (St.run x (script as s)) [])) (cmdWriteNames x (script as s))
extra-lemma {s} {ls} [] bs xs x (¬hz ∷ hf) = dsj , (extra-lemma3 bs xs x {!!} {!!} {!!} (subst (λ x₁ → HazardFree x₁ _ _ _) (cong (St.run x) refl) hf))
  where dsj : Disjoint (files ls) (cmdWriteNames x (script [] s))
        dsj x₂ with ∈-++⁻ (filesRead ls) (proj₁ x₂)
        ... | inj₁ ∈₁ = ¬hz (ReadWrite (proj₂ x₂) ∈₁)
        ... | inj₂ ∈₁ = ¬hz (WriteWrite (proj₂ x₂) ∈₁)
extra-lemma (x₂ ∷ as) bs xs x (_ ∷ hf) = extra-lemma as bs xs x hf

preserves-help2 : ∀ {s} {ls} as bs ys x → filesWrote (script-rec (reverse ys) s ls) ⊆ filesWrote (script-rec as s ls) ++ filesWrote (script-rec bs (St.run x (script as s)) [])
preserves-help2 = {!!}
preserves-help1 : ∀ {s} {ls} as bs ys x → filesRead (script-rec (reverse ys) s ls) ⊆ filesRead (script-rec as s ls) ++ filesRead (script-rec bs (St.run x (script as s)) [])
preserves-help1 = {!!}







dsj-helper : ∀ {s} {ls} xs x → Disjoint (files (script-rec xs s ls)) (cmdWriteNames x (script xs s))
dsj-helper xs x x₁ = {!!}

{- with extra-lemma as bs (reverse ys) x (subst₂ (λ x₂ x₃ → HazardFree s x₂ x₃ ls) ≡₁ (unfold-reverse x ys) hf)
... | a₁ , a₂ with ∈-++⁻ (filesRead (script-rec (reverse ys) _ ls)) (proj₁ x₁)
... | inj₁ ∈₁ with ∈-++⁻ (filesRead (script-rec as s ls)) (⊆₁ ∈₁) 
  where ⊆₁ : filesRead (script-rec (reverse ys) s ls) ⊆ filesRead (script-rec as s ls) ++ filesRead (script-rec bs (St.run x (script as s)) [])
                ⊆₁ = {!!}
        ... | inj₁ ∈₂ = a₁ (∈-++⁺ˡ ∈₂ , ∈as (proj₂ x₁))
        ... | inj₂ ∈₂ = a₂ (∈-++⁺ˡ ∈₂ , ∈as (proj₂ x₁))
        -- in filesWrite (script-rec (reverse ys) ...
        dsj x₁ | (a₁ , a₂) | inj₂ ∈₁ with ∈-++⁻ (filesWrote (script-rec as s ls)) (⊆₁ ∈₁)
          where ⊆₁ : filesWrote (script-rec (reverse ys) s ls) ⊆ filesWrote (script-rec as s ls) ++ filesWrote (script-rec bs (St.run x (script as s)) [])
                ⊆₁ = {!!}
        ... | inj₁ ∈₂ = a₁ (∈-++⁺ʳ (filesRead (script-rec as s ls)) ∈₂ , ∈as (proj₂ x₁))
        ... | inj₂ ∈₂ = a₂ (∈-++⁺ʳ (filesRead (script-rec bs (St.run x (script as s)) [])) ∈₂ , ∈as (proj₂ x₁)) -}

{- ∈as : ∀ {v} → v ∈ cmdWriteNames x (script (reverse ys) s) → v ∈ cmdWriteNames x (script as s)
        ∈as v∈ with helper5 (buildReadNames (St.run x (script as s)) bs) x {!!}
        ... | all₁ with writes≡ (script as s) (St.run x (script as s)) bs all₁
        ... | ≡₁ with helper3 as bs (reverse ys) x (subst (λ x₁ → Disjoint _ x₁) (sym ≡₁) {!!}) {!!}
        ... | x≡ = {!!}

        -}



preservesHazardFree : ∀ {s} {ls} xs ys → length xs ≡ length ys → xs ↭ ys → UniqueEvidence xs ys (map proj₁ ls) → HazardFree s xs (reverse ys) ls → HazardFree s (reverse ys) (reverse ys) ls
preservesHazardFree [] [] _ p _ hf = []
preservesHazardFree {s} {ls} xs (x ∷ ys) _ p (uxs , ux ∷ uys , uls , dsj) hf with ∈-∃++ (∈-resp-↭ (↭-sym p) (here refl))
... | (as , bs , ≡₁) with preserves-++ x (reverse ys) (reverse ys) {!!} dsj₄ {!!} {!!}
    (preservesHazardFree (as ++ bs) ys (↭-length ↭₂) ↭₂ (uas++bs , uys , uls , dsj₀) hf₁)
  where ↭₂ : as ++ bs ↭ ys
        ↭₂ = drop-mid as [] (subst (λ x₁ → x₁ ↭ x ∷ ys) ≡₁ p)
        uas++bs : Unique (as ++ bs)
        uas++bs = unique-drop-mid as (subst (λ x₁ → Unique x₁) ≡₁ uxs)
        dsj₀ : Disjoint (as ++ bs) (map proj₁ ls)
        dsj₀ x₂ with ∈-++⁻ as (proj₁ x₂)
        ... | inj₁ _∈as = dsj (subst (λ x₁ → _ ∈ x₁) (sym ≡₁) (∈-++⁺ˡ _∈as) , (proj₂ x₂))
        ... | inj₂ _∈bs = dsj (subst (λ x₁ → _ ∈ x₁) (sym ≡₁) (∈-++⁺ʳ as (there _∈bs)) , (proj₂ x₂))
        ⊆₁ : as ++ x ∷ bs ⊆ reverse ys ++ x ∷ []
        ⊆₁ x₁∈as++x∷bs = subst (λ x₂ → _ ∈ x₂)
                               (unfold-reverse x ys)
                               (reverse⁺ (∈-resp-↭ p (subst (λ x₂ → _ ∈ x₂) (sym ≡₁) x₁∈as++x∷bs)))
        hf₀ : HazardFree s (as ++ x ∷ bs) ((reverse ys) ++ x ∷ []) _
        hf₀ = subst₂ (λ x₂ x₃ → HazardFree s x₂ x₃ _) ≡₁ (unfold-reverse x ys) hf
        hf₁ : HazardFree s (as ++ bs) (reverse ys) _
        hf₁ = hf-drop-mid as bs (reverse ys) ⊆₁
                          (subst (λ x₁ → Unique x₁) ≡₁ uxs)
                          (subst (λ x₁ → Unique x₁) (unfold-reverse x ys) (unique-reverse (x ∷ ys) (ux ∷ uys)))
                          uls
                          (subst (λ x₁ → Disjoint x₁ _) ≡₁ dsj)
                          hf₀
        bs⊆reverse-ys : bs ⊆ reverse ys
        bs⊆reverse-ys x₃ = reverse⁺ (∈-resp-↭ ↭₂ (∈-++⁺ʳ as x₃))
        x∉reverse-ys : x ∉ reverse ys
        x∉reverse-ys x∈reverse-ys = lookup ux (reverse⁻ x∈reverse-ys) refl
        dsj₁ : Disjoint (cmdWriteNames x (script as _)) (buildWriteNames (St.run x (script as _)) bs)
        dsj₁ = hf=>disjointWW s x as bs (reverse ys) _  bs⊆reverse-ys x∉reverse-ys hf₀
        dsj₂ : Disjoint (cmdReadNames x (script as _)) (buildWriteNames (St.run x (script as _)) bs)
        dsj₂ = hf=>disjointRW s x as bs (reverse ys) _ bs⊆reverse-ys x∉reverse-ys hf₀
        dsj₃ : Disjoint (cmdWriteNames x (script as _)) (buildReadNames (St.run x (script as _)) bs)
        dsj₃ = hf=>disjointWR s x as bs (reverse ys) _ bs⊆reverse-ys x∉reverse-ys hf₀

        dsj₄ : Disjoint (files (script-rec (reverse ys) _ ls)) (cmdWriteNames x (script (reverse ys) _))
        dsj₄ = {!!}
... | a₂ = subst (λ x₁ → HazardFree _ x₁ x₁ _) (sym (unfold-reverse x ys)) a₂

preservesHazards : ∀ s ls b₁ b₂ → b₁ ⊆ b₂ → Unique b₁ → Unique b₂ → ¬ HazardFree s b₁ b₁ ls → ¬ HazardFree s b₂ b₁ ls
preservesHazards s ls b₁ b₂ ⊆₁ ue ue₁ ¬hf hf = ¬hf {!!} -- (preservesHazardFree s ls b₁ b₂ hf)
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
correct-speculation : ∀ s br bc → PreCond s br bc → ¬ HazardFree s bc bc [] ⊎ ≡toScript s br bc
\end{code}}
\begin{code}[hide]
correct-speculation s br bc pc = {!!}
\end{code}

\begin{code}[hide]
semi-correct2 : ∀ s m ls b₁ b₂ → DisjointBuild s b₁ → MemoryProperty m → UniqueEvidence b₁ b₂ (map proj₁ ls) → b₂ ↭ b₁ → ¬ HazardFree s b₁ b₂ ls ⊎ ¬ HazardFree s b₂ b₂ ls ⊎ ∃[ s₁ ](∃[ m₁ ](∃[ ls₁ ](rattle b₁ b₂ ((s , m) , ls) ≡ inj₂ ((s₁ , m₁) , ls₁) × ∀ f₁ → s₁ f₁ ≡ script b₂ s f₁)))
             -- ≡toScript (s , m) ls b₁ b₂ b₂
semi-correct2 s mm ls b₁ b₂ dsb mp ue b₂↭b₁ with hazardfree? s b₁ b₂ ls
... | no hz = inj₁ hz
... | yes hf with hazardfree? s b₂ b₂ ls
... | no hz = inj₂ (inj₁ hz)
... | yes hf₁ with completeness-inner (s , mm) ls b₁ b₂ (dsb , mp , ue) hf
... | (s₁ , mm₁) , ls₁ , ≡₁ = inj₂ (inj₂ (s₁ , mm₁ , ls₁ , ≡₁ , λ f₁ → {!!}))
-- sym (trans (reordered b₂ b₁ ls b₂↭b₁ ue {!!} hf f₁) (trans (script≡rattle-inner mm b₁ (λ f₂ → refl) dsb mp f₁) (cong-app (cong proj₁ (soundness-inner (s , mm) ls b₁ b₂ ≡₁)) f₁)))))
-- 
\end{code}


\newcommand{\correctP}{%
\begin{code}
semi-correct : ∀ s br bs → PreCond s br bs → ¬ HazardFree s br bs [] ⊎ ¬ HazardFree s bs bs [] ⊎ ≡toScript s br bs
semi-correct s br bs pc with hazardfree? s br bs []
... | no hz = inj₁ hz
... | yes hf₁ with completeness s br bs pc hf₁
... | (s₁ , m₁) , ls , ≡₁ = inj₂ (inj₂ (s₁ , m₁ , ls , ≡₁ , ∀≡))
  where ∀≡ : ∀ f₁ → s₁ f₁ ≡ script bs s f₁
        ∀≡ f₁ = sym (trans (reordered≡ s br bs pc hf₁ f₁)
                           (soundness s br bs (proj₁ pc) ≡₁ f₁))
\end{code}}


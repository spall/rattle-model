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

soundness-inner : ∀ {st₁} {ls₁} st ls b₁ b₂ → rattle b₁ b₂ (st , ls) ≡ inj₂ (st₁ , ls₁) → rattle-unchecked b₁ st ≡ st₁
soundness-inner st ls [] b₂ ≡₁ = cong proj₁ (inj₂-injective ≡₁)
soundness-inner (s , m) ls (x ∷ b₁) b₂  ≡₁ with runWError {b₂} x s m ls | inspect (runWError {b₂} x s m) ls
... | inj₂ (st₂ , ls₂) | [ ≡₂ ] with runSoundness s m ls st₂ ls₂ b₂ x ≡₂
... | ≡st₂ = subst (λ x₁ → rattle-unchecked b₁ x₁ ≡ _) (sym ≡st₂) (soundness-inner st₂ ls₂ b₁ b₂ ≡₁)

OKBuild : State → FileInfo → Build → Build → Set
OKBuild (s , mm) ls b₁ b₂ = DisjointBuild s b₁ × MemoryProperty mm × UniqueEvidence b₁ b₂ (map proj₁ ls)

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

completeness : ∀ s br bs → PreCond s br bs → HazardFree s br bs [] → ∃[ st ](∃[ ls ](rattle br bs ((s , []) , []) ≡ inj₂ (st , ls)))
completeness s br bc (dsb , ubr , ubc , _) hf = completeness-inner (s , []) [] br bc (dsb , ([] , ubr , (ubc , (Data.List.Relation.Unary.AllPairs.[] , g₁)))) hf
  where g₁ : Disjoint br []
        g₁ ()

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
≡toScript : FileSystem → Build → Build → Set
≡toScript s br bs = ∃[ s₁ ](∃[ m ](∃[ ls ](rattle br bs ((s , []) , []) ≡ inj₂ ((s₁ , m) , ls) × ∀ f₁ → s₁ f₁ ≡ script bs s f₁)))

script≡rattle-unchecked : ∀ s b → DisjointBuild s b → (∀ f₁ → script b s f₁ ≡ proj₁ (rattle-unchecked b (s , [])) f₁)
script≡rattle-unchecked s b dsb = script≡rattle-inner [] b (λ f₁ → refl) dsb []

soundness : ∀ {s₁} {m₁} {ls} s br bs → DisjointBuild s br → rattle br bs ((s , []) , []) ≡ inj₂ ((s₁ , m₁) , ls)
          → (∀ f₁ → script br s f₁ ≡ s₁ f₁)
soundness s br bc dsb ≡₁ f₁ = trans (script≡rattle-unchecked s br dsb f₁)
                                    (cong-app (,-injectiveˡ (soundness-inner (s , []) [] br bc ≡₁)) f₁)
-- correctness is if you have any build then either you get the right answer (the one the script gave) or you get an error and there was a hazard.
correct-rattle : ∀ s b → PreCond s b b → ¬ HazardFree s b b [] ⊎ ≡toScript s b b
correct-rattle s b pc with rattle b b ((s , []) , []) | inspect (rattle b b) ((s , []) , [])
... | inj₁ hz | [ ≡₁ ] = inj₁ g₁
  where g₁ : ¬ HazardFree s b b []
        g₁ hf with completeness s b b pc hf
        ... | a , fst , ≡₂ = contradiction (trans (sym ≡₁) ≡₂) λ ()
... | inj₂ ((s₁ , mm₁) , ls₁) | [ ≡₁ ] = inj₂ (s₁ , mm₁ , ls₁ , refl , ∀≡)
  where ∀≡ : ∀ f₁ → s₁ f₁ ≡ script b s f₁
        ∀≡ f₁ = sym (soundness s b b (proj₁ pc) ≡₁ f₁)

-- not provable atm
correct-speculation : ∀ s br bc → PreCond s br bc → ¬ HazardFree s bc bc [] ⊎ ≡toScript s br bc
correct-speculation s br bc pc = {!!}

semi-correct : ∀ s br bs → PreCond s br bs → ¬ HazardFree s br bs [] ⊎ ¬ HazardFree s bs bs [] ⊎ ≡toScript s br bs
semi-correct s br bs pc with hazardfree? s br bs []
... | no hz = inj₁ hz
... | yes hf₁ with completeness s br bs pc hf₁
... | (s₁ , m₁) , ls , ≡₁ = inj₂ (inj₂ (s₁ , m₁ , ls , ≡₁ , ∀≡))
  where ∀≡ : ∀ f₁ → s₁ f₁ ≡ script bs s f₁
        ∀≡ f₁ = sym (trans (reordered≡ s br bs pc hf₁ f₁)
                           (soundness s br bs (proj₁ pc) ≡₁ f₁))


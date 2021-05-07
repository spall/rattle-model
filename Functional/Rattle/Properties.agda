
open import Functional.State as St using (F ; System ; Memory ; Cmd ; trace ; extend ; State)

module Functional.Rattle.Properties (oracle : F) where

open import Agda.Builtin.Equality

open import Functional.Forward.Properties (oracle) using (cmdWrites ; cmdReadWrites ; IdempotentState ; IdempotentCmd ; ∈-resp-≡ ; lemma2 ; cmdIdempotent ; cmdReads)
open import Functional.Forward.Exec (oracle) using (get ; maybeAll ; run?)
open import Functional.File using (FileName ; FileContent)
open import Data.Bool using (true ; false ; if_then_else_)

open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∃-syntax)
open import Data.List.Relation.Unary.All using (All)
open import Data.List using (List ; map ; _++_ ; foldr ; _∷_ ; [])
open import Data.List.Properties using (∷-injective)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Relation.Binary.PropositionalEquality using (trans ; cong ; cong-app ; sym ; decSetoid ; cong₂ ; subst ; inspect ; [_])
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Function.Base using (_∘_)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Unary.Any using (tail)
open import Functional.Rattle.Exec (oracle) using (execWError ; FileInfo ; runWError ; run ; doRunCheck ; doRun ; checkWriteRead ; hasHazard ; exec)
open import Functional.Build using (Build)
open import Data.Sum using (inj₂ ; from-inj₂ ; inj₁ )
open import Data.Sum.Properties using (inj₂-injective)
open import Functional.Script.Exec (oracle) as Script hiding (exec)
open import Functional.Script.HazardFree (oracle) using (HazardFree)


data MemoryProperty : Memory -> Set where
 []   : MemoryProperty []
 Cons : {mm : Memory} (x : Cmd) -> (sys : System) -> (∀ f₁ → f₁ ∈ cmdReads x sys -> sys f₁ ≡ St.run oracle x sys f₁) -> MemoryProperty mm -> MemoryProperty ((x , map (λ f₁ → f₁ , (St.run oracle x sys) f₁) (cmdReadWrites x sys)) ∷ mm)

getProperty : {mm : Memory} (x : Cmd) -> MemoryProperty mm -> (x∈ : x ∈ map proj₁ mm) -> ∃[ sys ](get x mm x∈ ≡ map (λ f₁ → f₁ , (St.run oracle x sys) f₁) (cmdReadWrites x sys) × ∀ f₁ → f₁ ∈ cmdReads x sys -> sys f₁ ≡ St.run oracle x sys f₁)
getProperty x (Cons x₁ sys ∀₁ mp) x∈ with x ≟ x₁
... | yes x≡x₁ = sys , cong (λ x₂ → map (λ f₁ → f₁ , foldr extend sys (proj₂ (proj₁ (oracle x₂) sys)) f₁) (cmdReadWrites x₂ sys)) (sym x≡x₁) , λ f₁ x₂ → subst (λ x₃ → sys f₁ ≡ St.run oracle x₃ sys f₁) (sym x≡x₁) (∀₁ f₁ (subst (λ x₃ → f₁ ∈ map proj₁ (proj₁ (proj₁ (oracle x₃) sys))) x≡x₁ x₂))
... | no ¬x≡x₁ = getProperty x mp (tail ¬x≡x₁ x∈)


doRunSoundness : {st st₁ : State} {fi fi₁ : FileInfo} {rf : Build} (x : Cmd) -> doRunCheck st fi x rf ≡ inj₂ (st₁ , fi₁) -> doRun st x ≡ st₁
doRunSoundness {st} {st₁} {fi} {fi₁} {rf} x ≡₁ with hasHazard st fi x rf
... | nothing = cong proj₁ (inj₂-injective ≡₁)


runSoundness : {st st₁ : State} {fi fi₁ : FileInfo} {rf : Build} (x : Cmd) -> runWError st fi x rf ≡ inj₂ (st₁ , fi₁) -> run st x ≡ st₁
runSoundness {st} {st₁} {fi} {fi₁} {rf} x ≡₁ with run? x st
... | true = doRunSoundness {st} {st₁} {fi} {fi₁} {rf} x ≡₁
... | false = cong proj₁ (inj₂-injective ≡₁)

soundness : {st st₁ : State} {fi fi₁ : FileInfo} {rf : Build} (b : Build) -> execWError (st , fi) b rf ≡ inj₂ (st₁ , fi₁) -> exec st b ≡ st₁
soundness [] ≡₁ = cong proj₁ (inj₂-injective ≡₁)
soundness {st} {st₁} {fi} {fi₁} {rf} (x ∷ b) ≡₁ with runWError st fi x rf | inspect (runWError st fi x) rf
... | inj₂ (st₂ , fi₂) | [ ≡₂ ] with run? x st | runSoundness {st} {st₂} {fi} {fi₂} {rf} x ≡₂
... | false | st≡st₂ = soundness b (subst (λ x₁ → execWError (x₁ , fi₂) b rf ≡ _) (sym st≡st₂) ≡₁)
... | true | ≡₃ = soundness b (subst (λ x₁ → execWError (x₁ , fi₂) b rf ≡ _) (sym ≡₃) ≡₁)



-- runWError ≡ run if runWError ≡ inj₂

-- prove if no errors ; do run and dorun check are the same ; aka give same system

-- completeness, does rattle actually work for pieces of software? 

-- if there is no hazard then run with error produces right; use hazardfree evidence
completeness : {sys : System} {mm : Memory} {fi : FileInfo} (b : Build) -> HazardFree sys b _ -> ∃[ st ](∃[ fi₁ ](execWError ((sys ,  mm) , fi) b _ ≡ inj₂ (st , fi₁)))
completeness {sys} {mm} {fi} [] hf = (sys , mm) , (fi , refl)
completeness (x ∷ b) hf = {!!}

-- if there is a hazard we do produce an error



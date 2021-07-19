{-# OPTIONS --allow-unsolved-metas #-}
open import Functional.State as St using (State ; F ; Cmd ; System ; trace ; Memory)

module Functional.Rattle.Exec (oracle : F) where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Nat.Properties as N hiding (_≟_)
open import Data.Bool using (Bool ; if_then_else_ ; false ; true ; not)
open import Data.List using (List ; [] ; _∷_ ; map ; filter ; _++_ ; foldr ; all ; concatMap ; reverse; _∷ʳ_)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Maybe.Relation.Binary.Pointwise using (dec)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∃-syntax ; Σ-syntax)
open import Data.Product.Properties using (≡-dec)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-decidable ; ≡×≡⇒≡ ; ≡⇒≡×≡ )
open import Function.Base using (_∘_)
open import Functional.File using (FileName ; FileContent)
open import Functional.Build using (Build ; NBuild)
open import Relation.Binary using (Decidable)
open import Relation.Nullary.Decidable as Dec using (isYes ; map′)
open import Relation.Nullary.Negation using (¬?)
open import Functional.Forward.Exec (oracle) using (run?)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; map₂)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_ ; _∈_)

decp : Decidable _≡_
decp x y = map′ ≡×≡⇒≡ ≡⇒≡×≡ (×-decidable _≟_ N._≟_ x y)

open import Data.List.Membership.DecPropositional (decp) as P hiding (_∈?_ ; _∈_)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Functional.Script.Exec (oracle)  as S hiding (exec)
open import Common.List.Properties using (_before_en_ ; before-∷)
open import Functional.Script.Hazard (oracle) using (Hazard ; FileInfo ; cmdReads ; cmdWrites ; save ; WriteWrite ; ReadWrite ; Speculative ; filesRead ; filesWrote ; cmdRead ; cmdWrote ; cmdsRun)

doRun : State -> Cmd -> State
doRun (sys , mm) cmd = let sys₂ = St.run oracle cmd sys in
                           (sys₂ , St.save cmd ((cmdReads sys cmd) ++ (cmdWrites sys cmd)) sys₂ mm)

{- check for hazards

speculative write read
write write
read write

-}

{- check for speculative hazard
  

   check for writewrite hazard
   check for readwrite hazard

 1. speculative
 -- 
2. write write
3. read write

-}

∃Intersection : ∀ ls₁ ls₂ → Maybe (∃[ v ](v ∈ ls₁ × v ∈ ls₂))
∃Intersection [] ls₂ = nothing
∃Intersection (x ∷ ls₁) ls₂ with x ∈? ls₂
... | yes x∈ls₂ = just (x , here refl , x∈ls₂)
... | no x∉ls₂ with ∃Intersection ls₁ ls₂
... | nothing = nothing
... | just (v , v∈ls₁ , v∈ls₂) = just (v , there v∈ls₁ , v∈ls₂)

{- is the command required? 
   is x in b?
   are all commands before x in b in ls?
-}
required? : (x : (Cmd × ℕ)) (b ls : NBuild) → Bool
required? x [] ls = false
required? x (x₁ ∷ b) ls with ×-decidable _≟_ N._≟_ x x₁
... | no ¬x≡x₁ = required? x b ls
... | yes x≡x₁ = subset? b ls
  where subset? : (ls₁ ls₂ : NBuild) → Bool
        subset? [] ls₂ = true
        subset? (x ∷ ls₁) ls₂ with x P.∈? ls₁
        ... | yes x∈ = subset? ls₁ ls₂
        ... | no x∉ = false


{- is there a speculative hazard?-}
{- first command is writer; 2nd is reader; ignoring x -}

{- 1. lets check if x is speculative or required. 
   2. if its required; then we look for earlier commands in ls whose writes intersect with the reads of x. 
   3. 
-}
∃Speculative1 : ∀ ls b ran → Maybe (∃[ x₁ ](∃[ x₂ ](∃[ v ](x₂ before x₁ en (cmdsRun ls) × ¬ x₁ before x₂ en b × v ∈ cmdRead ls x₂ × v ∈ cmdWrote ls x₁))))
∃Speculative1 [] b ran = nothing
∃Speculative1 (x ∷ ls) b ran with required? (proj₁ x) b ((cmdsRun ls) ++ ran)
... | true = {!!}
... | false with ∃Speculative1 ls b ((proj₁ x) ∷ ran)
... | nothing = nothing
... | just (x₁ , x₂ , v , bf , ¬bf , v∈cr , v∈cw)
  = just (x₁ , x₂ , v , before-∷ x₂ x₁ (proj₁ x) (cmdsRun ls) bf , ¬bf , {!!} , {!!})

∃Speculative : ∀ s x b ls → Maybe (Hazard s x b ls)
∃Speculative s x b ls with ∃Speculative1 (save x (cmdReads s x) (cmdWrites s x) ls) b []
... | nothing = nothing
... | just (x₁ , x₂ , v , bf , ¬bf , v∈cr , v∈cw) = just (Speculative s x b ls x₁ x₂ v bf ¬bf v∈cr v∈cw)

{- is there a read/write or write/write hazard? -}
∃WriteWrite : ∀ s x b ls → Maybe (Hazard s x b ls)
∃WriteWrite s x b ls with ∃Intersection (cmdWrites s x) (filesWrote ls)
... | nothing = nothing
... | just (v , v∈ws , v∈wrotes) = just (WriteWrite s x ls v v∈ws v∈wrotes)

∃ReadWrite : ∀ s x b ls → Maybe (Hazard s x b ls)
∃ReadWrite s x b ls with ∃Intersection (cmdWrites s x) (filesRead ls)
... | nothing = nothing
... | just (v , v∈ws , v∈reads) = just (ReadWrite s x ls v v∈ws v∈reads)

checkHazard : ∀ s x b ls → Maybe (Hazard s x b ls)
checkHazard s x b ls with ∃WriteWrite s x b ls
... | just hz = just hz
... | nothing with ∃Speculative s x b ls
... | just hz = just hz
... | nothing = ∃ReadWrite s x b ls

doRunWError : ∀ b → (((s , mm) , ls) : State × FileInfo) → (x : Cmd) → Hazard s x b ls ⊎ State × FileInfo
doRunWError b ((s , mm) , ls) x with checkHazard s x b ls
... | just hz = inj₁ hz
... | nothing = let sys₁ = St.run oracle x s in
                inj₂ ((sys₁ , St.save x ((cmdReads s x) ++ (cmdWrites s x)) sys₁ mm)
                      , save x (cmdReads s x) (cmdWrites s x) ls)

run : State -> Cmd -> State
run st cmd = if (run? cmd st)
             then doRun st cmd
             else st

runWError : ∀ b → (((s , mm) , ls) : State × FileInfo) → (x : Cmd) → Hazard s x b ls ⊎ State × FileInfo
runWError b (st , ls) x with (run? x st)
... | true = doRunWError b (st , ls) x
... | false = inj₂ (st , ls)

exec : State -> Build -> State
exec st [] = st
exec st (x ∷ b) = exec (run st x) b

execWError : State × FileInfo → (b₁ : Build) → (b₂ : NBuild) → ∃[ s ](∃[ x ](∃[ ls ](Hazard s x b₂ ls))) ⊎ State × FileInfo
execWError st [] b₂ = inj₂ st
execWError st (x ∷ b₁) b₂ with runWError b₂ st x
... | inj₁ hz = inj₁ (proj₁ (proj₁ st) , x , proj₂ st , hz)
... | inj₂ a = execWError a b₁ b₂

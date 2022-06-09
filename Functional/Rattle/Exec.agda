open import Functional.State using (State ; Oracle ; Cmd ; FileSystem ; Memory) renaming (save to store)

module Functional.Rattle.Exec (oracle : Oracle) where

open import Functional.State.Helpers (oracle) as St hiding (run)
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as N using (1+n≰n) 
open import Data.Bool using (Bool ; if_then_else_ ; false ; true ; not)
open import Data.List using (List ; [] ; _∷_ ; map ; filter ; _++_ ; foldr ; all ; concatMap ; reverse; _∷ʳ_)
open import Data.List.Properties using (∷-injectiveʳ ; ∷-injectiveˡ ; ∷-injective)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Maybe.Relation.Binary.Pointwise using (dec)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∃-syntax ; Σ-syntax)
open import Data.Product.Properties using (≡-dec ; ,-injectiveˡ ; ,-injectiveʳ)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-decidable ; ≡×≡⇒≡ ; ≡⇒≡×≡ )
open import Function.Base using (_∘_)
open import Functional.File using (FileName ; FileContent)
open import Functional.Build (oracle) using (Build ; UniqueEvidence)
open import Relation.Binary using (Decidable)
open import Relation.Nullary.Decidable as Dec using (isYes ; map′)
open import Relation.Nullary.Negation using (¬? ; contradiction)
open import Functional.Forward.Exec (oracle) using (run?)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; map₂)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_ ; _∈_ ; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Common.List.Properties using (_before_∈_ ; before-∷)
open import Functional.Script.Hazard (oracle) using (Hazard ; WriteWrite ; ReadWrite ; Speculative ; filesRead ; filesWrote ; cmdRead ; cmdWrote ; cmdsRun ; FileInfo ; ∈-cmdWrote∷ ; ∈-cmdRead∷ ; ∃Hazard ; before?) renaming (save to rec)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Relation.Binary.PropositionalEquality using (cong ; trans ; sym ; subst ; _≢_)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)

doRunR : State -> Cmd -> State
doRunR (s , m) x = let s₂ = St.run x s in
                           (s₂ , store x ((cmdReadNames x s) ++ (cmdWriteNames x s)) s₂ m)

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
required? : (x : Cmd) (b ls bf : Build) → Maybe (x ∈ b)
required? x [] ls _ = nothing
required? x (x₁ ∷ b) ls bf with x ≟ x₁
... | no ¬x≡x₁ with required? x b ls (x₁ ∷ bf)
... | nothing = nothing
... | just x∈b = just (there x∈b)
required? x (x₁ ∷ b) ls bf | yes x≡x₁ with subset? bf ls
  where subset? : (ls₁ ls₂ : Build) → Bool
        subset? [] ls₂ = true
        subset? (x ∷ ls₁) ls₂ with x ∈? ls₁
        ... | yes x∈ = subset? ls₁ ls₂
        ... | no x∉ = false
... | true = just (here x≡x₁)
... | false = nothing

∃Speculative2 : ∀ x₂ b ls₁ ls rs → Maybe (∃[ x₁ ](∃[ v ](x₁ ∈ ls₁ × ¬ (x₁ before x₂ ∈ b) × v ∈ rs × v ∈ cmdWrote ls x₁)))
∃Speculative2 x₂ b [] ls rs = nothing
∃Speculative2 x₂ b (x ∷ ls₁) ls rs  with before? x x₂ b
... | yes bf with ∃Speculative2 x₂ b ls₁ ls rs
... | nothing = nothing
... | just (x₁ , v , x₁∈ls , ¬bf , v∈rs , v∈ws)
  = just (x₁ , v , there x₁∈ls , ¬bf , v∈rs , v∈ws) -- ∈-cmdWrote∷ x x₁ ls v∈ws (lookup px x₁∈ls))
∃Speculative2 x₂ b (x ∷ ls₁) ls rs | no ¬bf with ∃Intersection rs (cmdWrote ls x)
... | just (v , v∈rs , v∈ws) = just (x , v , here refl , ¬bf , v∈rs , v∈ws)
... | nothing with ∃Speculative2 x₂ b ls₁ ls rs
... | nothing = nothing
... | just (x₁ , v , x₁∈ls , ¬bf₁ , v∈rs , v∈ws)
  = just (x₁ , v , there x₁∈ls , ¬bf₁ , v∈rs , v∈ws) -- ∈-cmdWrote∷ x x₁ ls v∈ws (lookup px x₁∈ls))

∃Speculative1 : ∀ ls₁ ls {b} (ran : Build) → Maybe (∃[ x₁ ](∃[ x₂ ](∃[ v ]((x₂ before x₁ ∈ ls₁) × x₂ ∈ b × ¬ (x₁ before x₂ ∈ b) × v ∈ cmdRead ls x₂ × v ∈ cmdWrote ls x₁))))
∃Speculative1 [] ls ran = nothing
∃Speculative1 (x ∷ ls₁) ls {b} ran with required? x b (ls₁ ++ ran) []
... | just x∈b with ∃Speculative2 x b ls₁ ls (cmdRead ls x)
... | just (x₁ , v , x₁∈ls , ¬bf , v∈rs , v∈ws)
  = just (x₁ , x , v , ([] , ls₁ , refl , x₁∈ls) , x∈b , ¬bf , v∈rs
         , v∈ws)
... | nothing with ∃Speculative1 ls₁ ls (x ∷ ran)
... | nothing = nothing
... | just (x₁ , x₂ , v , bf@(xs , ys , ≡₁ , x₁∈ys) , x₂∈b , ¬bf , v∈cr , v∈cw)
  = just (x₁ , x₂ , v , before-∷ x₂ x₁ x ls₁ bf , x₂∈b , ¬bf
         , v∈cr
         , v∈cw)
∃Speculative1 (x ∷ ls₁) ls ran | nothing with ∃Speculative1 ls₁ ls (x ∷ ran)
... | nothing = nothing
... | just (x₁ , x₂ , v , bf@(xs , ys , ≡₁ , x₁∈ys) , x₂∈b , ¬bf , v∈cr , v∈cw)
  = just (x₁ , x₂ , v , before-∷ x₂ x₁ x ls₁ bf , x₂∈b , ¬bf
         , v∈cr , v∈cw)

∃Speculative : ∀ s x {b} ls → Maybe (Hazard s x b ls)
∃Speculative s x {b} ls with ∃Speculative1 (x ∷ cmdsRun ls) (rec s x ls) []
... | nothing = nothing
... | just (x₁ , x₂ , v , bf , x₁∈b , ¬bf , v∈cr , v∈cw)
  = just (Speculative x₁ x₂ bf x₁∈b ¬bf v∈cr v∈cw)


{- is there a read/write or write/write hazard? -}
∃WriteWrite : ∀ s x {b} ls → Maybe (Hazard s x b ls)
∃WriteWrite s x ls with ∃Intersection (cmdWriteNames x s) (filesWrote ls)
... | nothing = nothing
... | just (v , v∈ws , v∈wrotes) = just (WriteWrite v∈ws v∈wrotes)

∃ReadWrite : ∀ s x {b} ls → Maybe (Hazard s x b ls)
∃ReadWrite s x ls with ∃Intersection (cmdWriteNames x s) (filesRead ls)
... | nothing = nothing
... | just (v , v∈ws , v∈reads) = just (ReadWrite v∈ws v∈reads)

checkHazard : ∀ s x {b} ls → Maybe (Hazard s x b ls)
checkHazard s x ls with ∃WriteWrite s x ls
... | just hz = just hz
... | nothing with ∃Speculative s x ls
... | just hz = just hz
... | nothing = ∃ReadWrite s x ls

doRunWError : ∀ {b} (((s , m) , ls) : State × FileInfo) → (x : Cmd) → Hazard s x b ls ⊎ State × FileInfo
doRunWError ((s , mm) , ls) x with checkHazard s x ls
... | just hz = inj₁ hz
... | nothing = inj₂ (doRunR (s , mm) x , rec s x ls)

runR : Cmd → (FileSystem × Memory)
     → (FileSystem × Memory)
runR cmd st = if (run? cmd st)
             then doRunR st cmd
             else st

g₂ : ∀ {x} xs → x ∉ xs → All (λ y → ¬ x ≡ y) xs
g₂ [] x∉xs = All.[]
g₂ (x ∷ xs) x∉xs = (λ x₃ → x∉xs (here x₃)) All.∷ (g₂ xs λ x₃ → x∉xs (there x₃))

runWError : ∀ {b} x s m ls
  → Hazard s x b ls ⊎ (FileSystem × Memory) × FileInfo
runWError x s m ls with (run? x (s , m))
... | false = inj₂ ((s , m) , ls)
... | true with checkHazard s x ls
... | just hz = inj₁ hz
... | nothing = inj₂ (doRunR (s , m) x , rec s x ls)

rattle-unchecked : Build → (FileSystem × Memory)
                 → (FileSystem × Memory)
rattle-unchecked [] st = st
rattle-unchecked (x ∷ b) st = rattle-unchecked b (runR x st)

rattle : (br bs : Build) → (FileSystem × Memory) × FileInfo
       → ∃Hazard bs ⊎ (FileSystem × Memory) × FileInfo
rattle [] bs st = inj₂ st
rattle (x ∷ b₁) bs ((s , m) , ls) with runWError x s m ls
... | inj₁ hz = inj₁ (s , x , ls , hz)
... | inj₂ (st₁ , ls₁) = rattle b₁ bs (st₁ , ls₁)

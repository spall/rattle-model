open import Functional.State as St using (State ; F ; Cmd ; System ; trace ; Memory)

module Functional.Rattle.Exec (oracle : F) where

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
open import Functional.Build using (Build ; ΣNBuild ; Unique-> ; NBuild ; ¬≡-⊎->⇒¬≡)
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
open import Functional.Script.Exec (oracle)  as S hiding (exec)
open import Common.List.Properties using (_before_en_ ; before-∷)
open import Functional.Script.Hazard (oracle) using (Hazard ; cmdReads ; cmdWrites ; save ; WriteWrite ; ReadWrite ; Speculative ; filesRead ; filesWrote ; cmdRead ; cmdWrote ; cmdsRun ; FileInfo ; ∈-cmdWrote∷ ; ∈-cmdRead∷)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Relation.Binary.PropositionalEquality using (cong ; trans ; sym ; subst ; _≢_)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)

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
   are all commands before x in b (and b is reversed so) in ls?
-}
-- wow this was actually bugged before haha
required? : (x : Cmd) (b ls : Build) → Maybe (x ∈ b)
required? x [] ls = nothing
required? x (x₁ ∷ b) ls with x ≟ x₁
... | no ¬x≡x₁ with required? x b ls
... | nothing = nothing
... | just x∈b = just (there x∈b)
required? x (x₁ ∷ b) ls | yes x≡x₁ with subset? b ls
  where subset? : (ls₁ ls₂ : Build) → Bool
        subset? [] ls₂ = true
        subset? (x ∷ ls₁) ls₂ with x ∈? ls₁
        ... | yes x∈ = subset? ls₁ ls₂
        ... | no x∉ = false
... | true = just (here x≡x₁)
... | false = nothing


{- I shouldn't have to say x is in this list, but if I dont I have to deal with the case 
   where b is empty and I can't seem to get agda to agree the empty list doesnt equal a
   non empty list easily and I can't be bothered to figure this out right now. -}
∃-¬Before : ∀ x x₁ b → Unique b → x₁ ∈ b → (¬ x before x₁ en b) ⊎ (x before x₁ en b)
∃-¬Before x x₁ (x₂ ∷ b) (px ∷ u) x₁∈b with x₁ ≟ x₂
... | yes x₁≡x₂ = inj₁ g₁
  where g₁ : x before x₁ en (x₂ ∷ b) → ⊥
        g₁ ([] , ys , ≡₁ , x₁∈ys) with ∷-injective ≡₁
        ... | x₂≡x , b≡ys = lookup px (subst (λ x₃ → x₁ ∈ x₃) (sym b≡ys) x₁∈ys) (sym x₁≡x₂)
        g₁ (x₃ ∷ xs , ys , ≡₁ , x₁∈ys) = lookup px (subst (λ x₄ → x₁ ∈ x₄) (sym (∷-injectiveʳ ≡₁)) (∈-++⁺ʳ xs (there x₁∈ys))) (sym x₁≡x₂)
... | no ¬x₁≡x₂ with x₂ ≟ x
... | yes x₂≡x = inj₂ ([] , b , cong (_∷ b) x₂≡x , tail ¬x₁≡x₂ x₁∈b)
... | no ¬x≡x₂ with ∃-¬Before x x₁ b u (tail ¬x₁≡x₂ x₁∈b)
... | inj₂ (xs , ys , ≡₁ , x₁∈ys) = inj₂ (x₂ ∷ xs , ys , cong (x₂ ∷_) ≡₁ , x₁∈ys)
... | inj₁ ¬bf = inj₁ g₁
  where g₁ : x before x₁ en (x₂ ∷ b) → ⊥
        g₁ ([] , ys , ≡₁ , x₁∈ys) = ¬x≡x₂ (∷-injectiveˡ ≡₁)
        g₁ (x₃ ∷ xs , ys , ≡₁ , x₁∈ys) = ¬bf (xs , ys , ∷-injectiveʳ ≡₁ , x₁∈ys)


∃Speculative2 : ∀ x₂ b ls rs → Unique (map proj₁ ls) → Unique b → x₂ ∈ b → Maybe (∃[ x₁ ](∃[ v ](x₁ ∈ (cmdsRun ls) × ¬ x₁ before x₂ en b × v ∈ rs × v ∈ cmdWrote ls x₁)))
∃Speculative2 x₂ b [] rs uls ub x₂∈b = nothing
∃Speculative2 x₂ b (x ∷ ls) rs (px ∷ uls) ub x₂∈b with ∃-¬Before (proj₁ x) x₂ b ub x₂∈b
... | inj₂ bf with ∃Speculative2 x₂ b ls rs uls ub x₂∈b
... | nothing = nothing
... | just (x₁ , v , x₁∈ls , ¬bf , v∈rs , v∈ws)
  = just (x₁ , v , there x₁∈ls , ¬bf , v∈rs , ∈-cmdWrote∷ v x x₁ ls v∈ws (lookup px x₁∈ls))
∃Speculative2 x₂ b (x ∷ ls) rs (px ∷ uls) ub x₂∈b | inj₁ ¬bf with ∃Intersection rs (cmdWrote (x ∷ ls) (proj₁ x))
... | just (v , v∈rs , v∈ws) = just (proj₁ x , v , here refl , ¬bf , v∈rs , v∈ws)
... | nothing with ∃Speculative2 x₂ b ls rs uls ub x₂∈b
... | nothing = nothing
... | just (x₁ , v , x₁∈ls , ¬bf₁ , v∈rs , v∈ws)
  = just (x₁ , v , there x₁∈ls , ¬bf₁ , v∈rs , ∈-cmdWrote∷ v x x₁ ls v∈ws (lookup px x₁∈ls))

∃Speculative1 : ∀ ls b (ran : Build) → Unique (map proj₁ ls) → Unique b → Maybe (∃[ x₁ ](∃[ x₂ ](∃[ v ](x₂ before x₁ en (cmdsRun ls) × x₂ ∈ b × ¬ x₁ before x₂ en b × v ∈ cmdRead ls x₂ × v ∈ cmdWrote ls x₁))))
∃Speculative1 [] b ran uls ub = nothing
∃Speculative1 (x ∷ ls) b ran (px ∷ uls) ub with required? (proj₁ x) b ((cmdsRun ls) ++ ran)
... | just x∈b with ∃Speculative2 (proj₁ x) b ls (cmdRead (x ∷ ls) (proj₁ x)) uls ub x∈b
... | just (x₁ , v , x₁∈ls , ¬bf , v∈rs , v∈ws)
  = just (x₁ , proj₁ x , v , ([] , cmdsRun ls , refl , x₁∈ls) , x∈b , ¬bf , v∈rs
         , ∈-cmdWrote∷ v x x₁ ls v∈ws (lookup px x₁∈ls))
... | nothing with ∃Speculative1 ls b ((proj₁ x) ∷ ran) uls ub
... | nothing = nothing
... | just (x₁ , x₂ , v , bf@(xs , ys , ≡₁ , x₁∈ys) , x₂∈b , ¬bf , v∈cr , v∈cw)
  = just (x₁ , x₂ , v , before-∷ x₂ x₁ (proj₁ x) (cmdsRun ls) bf , x₂∈b , ¬bf
         , ∈-cmdRead∷ v x x₂ ls v∈cr
           (lookup px (subst (λ x₃ → x₂ ∈ x₃) (sym ≡₁) (∈-++⁺ʳ xs (here refl))))
         , ∈-cmdWrote∷ v x x₁ ls v∈cw
           (lookup px (subst (λ x₃ → x₁ ∈ x₃) (sym ≡₁) (∈-++⁺ʳ xs (there x₁∈ys)))))
∃Speculative1 (x ∷ ls) b ran (px ∷ uls) ub | nothing with ∃Speculative1 ls b ((proj₁ x) ∷ ran) uls ub
... | nothing = nothing
... | just (x₁ , x₂ , v , bf@(xs , ys , ≡₁ , x₁∈ys) , x₂∈b , ¬bf , v∈cr , v∈cw)
  = just (x₁ , x₂ , v , before-∷ x₂ x₁ (proj₁ x) (cmdsRun ls) bf , x₂∈b , ¬bf
         , ∈-cmdRead∷ v x x₂ ls v∈cr
           (lookup px (subst (λ x₃ → x₂ ∈ x₃) (sym ≡₁) (∈-++⁺ʳ xs (here refl))))
         , ∈-cmdWrote∷ v x x₁ ls v∈cw
           (lookup px (subst (λ x₃ → x₁ ∈ x₃) (sym ≡₁) (∈-++⁺ʳ xs (there x₁∈ys)))))


∃Speculative : ∀ s x b ls → Unique (x ∷ (map proj₁ ls)) → Unique b → Maybe (Hazard s x b ls)
∃Speculative s x b ls uls ub with ∃Speculative1 (save x (cmdReads s x) (cmdWrites s x) ls) b [] uls ub
... | nothing = nothing
... | just (x₁ , x₂ , v , bf , x₁∈b , ¬bf , v∈cr , v∈cw)
  = just (Speculative s x b ls x₁ x₂ v bf x₁∈b ¬bf v∈cr v∈cw)


{- is there a read/write or write/write hazard? -}
∃WriteWrite : ∀ s x b ls → Maybe (Hazard s x b ls)
∃WriteWrite s x b ls with ∃Intersection (cmdWrites s x) (filesWrote ls)
... | nothing = nothing
... | just (v , v∈ws , v∈wrotes) = just (WriteWrite s x ls v v∈ws v∈wrotes)

∃ReadWrite : ∀ s x b ls → Maybe (Hazard s x b ls)
∃ReadWrite s x b ls with ∃Intersection (cmdWrites s x) (filesRead ls)
... | nothing = nothing
... | just (v , v∈ws , v∈reads) = just (ReadWrite s x ls v v∈ws v∈reads)

checkHazard : ∀ s x b ls → Unique (x ∷ (map proj₁ ls)) → Unique b → Maybe (Hazard s x b ls)
checkHazard s x b ls uls ub with ∃WriteWrite s x b ls
... | just hz = just hz
... | nothing with ∃Speculative s x b ls uls ub
... | just hz = just hz
... | nothing = ∃ReadWrite s x b ls

g₂ : ∀ {x} xs → x ∉ xs → All (λ y → ¬ x ≡ y) xs
g₂ [] x∉xs = All.[]
g₂ (x ∷ xs) x∉xs = (λ x₃ → x∉xs (here x₃)) All.∷ (g₂ xs λ x₃ → x∉xs (there x₃))


doRunWError : ∀ b → (((s , mm) , ls) : State × FileInfo) → (x : Cmd) → x ∉ map proj₁ ls → Unique (map proj₁ ls) → Unique b → Hazard s x b ls ⊎ ∃[ st ](Σ[ ls₁ ∈ FileInfo ](Unique (map proj₁ ls₁) × (map proj₁ ls₁) ≡ x ∷ (map proj₁ ls)))
doRunWError b ((s , mm) , ls) x x∉ls uls ub with checkHazard s x b ls (g₂ (map proj₁ ls) x∉ls ∷ uls) ub
... | just hz = inj₁ hz
... | nothing = let sys₁ = St.run oracle x s in
                inj₂ ((sys₁ , St.save x ((cmdReads s x) ++ (cmdWrites s x)) sys₁ mm) , save x (cmdReads s x) (cmdWrites s x) ls , g₂ (map proj₁ ls) x∉ls ∷ uls , refl)


run : State -> Cmd -> State
run st cmd = if (run? cmd st)
             then doRun st cmd
             else st

runWError : ∀ b → (((s , mm) , ls) : State × FileInfo) → (x : Cmd) → Unique (map proj₁ ls) → Unique b → x ∉ (map proj₁ ls) → Hazard s x b ls ⊎ ∃[ st ](∃[ ls₁ ](Unique (map proj₁ ls₁) × ((map proj₁ ls₁) ≡ (map proj₁ ls) ⊎ (map proj₁ ls₁) ≡ x ∷ (map proj₁ ls))))
runWError b (st , ls) x uls ub x∉ with (run? x st)
... | false = inj₂ (st , ls , uls , inj₁ refl)
... | true with doRunWError b (st , ls) x x∉ uls ub
... | inj₁ hz = inj₁ hz
... | inj₂ (st₁ , ls₁ , uls₁ , ≡₁) = inj₂ (st₁ , ls₁ , uls₁ , inj₂ ≡₁)

exec : State -> Build -> State
exec st [] = st
exec st (x ∷ b) = exec (run st x) b

execWError : ∀ (st@(_ , ls) : State × FileInfo) b₁ b₂ → Unique b₁ → Unique b₂ → Unique (map proj₁ ls) → Disjoint b₁ (map proj₁ ls) → ∃[ s ](∃[ x ](∃[ ls ](Hazard s x b₂ ls))) ⊎ State × FileInfo
execWError st [] b₂ ub₁ ub₂ uls dsj = inj₂ st
execWError st (x ∷ b₁) b₂ (px ∷ ub₁) ub₂ uls dsj with runWError b₂ st x uls ub₂ λ x₁ → dsj (here refl , x₁)
... | inj₁ hz = inj₁ (proj₁ (proj₁ st) , x , proj₂ st , hz)
... | inj₂ (st₁ , ls₁ , uls₁ , inj₁ ≡₁) = execWError (st₁ , ls₁) b₁ b₂ ub₁ ub₂ uls₁ λ x₂ → dsj (there (proj₁ x₂) , subst (λ x₃ → _ ∈ x₃) ≡₁ (proj₂ x₂))
... | inj₂ (st₁ , ls₁ , uls₁ , inj₂ ≡₁) = execWError (st₁ , ls₁) b₁ b₂ ub₁ ub₂ uls₁ λ x₁ → dsj (there (proj₁ x₁) , g₁ (proj₂ x₁) ≡₁ λ v≡x → lookup px (proj₁ x₁) (sym v≡x))
  where g₁ : ∀ {v} {ls₁} {ls₂} {x} → v ∈ ls₁ → ls₁ ≡ x ∷ ls₂ → ¬ v ≡ x → v ∈ ls₂
        g₁ v∈ls₁ ls₁≡x∷ls₂ ¬v≡x = tail ¬v≡x (subst (λ x₁ → _ ∈ x₁) ls₁≡x∷ls₂ v∈ls₁)

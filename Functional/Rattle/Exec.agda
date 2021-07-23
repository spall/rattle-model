open import Functional.State as St using (State ; F ; Cmd ; System ; trace ; Memory)

module Functional.Rattle.Exec (oracle : F) where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as N using (1+n≰n) 
open import Data.Bool using (Bool ; if_then_else_ ; false ; true ; not)
open import Data.List using (List ; [] ; _∷_ ; map ; filter ; _++_ ; foldr ; all ; concatMap ; reverse; _∷ʳ_)
open import Data.List.Properties using (∷-injectiveʳ ; ∷-injectiveˡ)
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
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_ ; _∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)

open import Data.Empty using (⊥)

decp : Decidable _≡_
decp x y = map′ ≡×≡⇒≡ ≡⇒≡×≡ (×-decidable _≟_ N._≟_ x y)

open import Data.List.Membership.DecPropositional (decp) as P hiding (_∈?_ ; _∈_)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Functional.Script.Exec (oracle)  as S hiding (exec)
open import Common.List.Properties using (_before_en_ ; before-∷)
open import Functional.Script.Hazard (oracle) using (Hazard ; ΣFileInfo ; cmdReads ; cmdWrites ; save ; WriteWrite ; ReadWrite ; Speculative ; filesRead ; filesWrote ; cmdRead ; cmdWrote ; cmdsRun ; FileInfo ; ∈-cmdWrote∷ ; ∈-cmdRead∷)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Relation.Binary.PropositionalEquality using (cong ; trans ; sym ; subst ; _≢_)

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
required? : (x : (Cmd × ℕ)) (b ls : NBuild) → Maybe (x P.∈ b)
required? x [] ls = nothing
required? x (x₁ ∷ b) ls with ×-decidable _≟_ N._≟_ x x₁
... | no ¬x≡x₁ with required? x b ls
... | nothing = nothing
... | just x∈b = just (there x∈b)
required? x (x₁ ∷ b) ls | yes x≡x₁ with subset? b ls
  where subset? : (ls₁ ls₂ : NBuild) → Bool
        subset? [] ls₂ = true
        subset? (x ∷ ls₁) ls₂ with x P.∈? ls₁
        ... | yes x∈ = subset? ls₁ ls₂
        ... | no x∉ = false
... | true = just (here (≡×≡⇒≡ x≡x₁))
... | false = nothing


{- I shouldn't have to say x is in this list, but if I dont I have to deal with the case 
   where b is empty and I can't seem to get agda to agree the empty list doesnt equal a
   non empty list easily and I can't be bothered to figure this out right now. -}
∃-¬Before : ∀ x x₁ b → Unique-> b → x P.∈ b → Maybe (¬ x before x₁ en b)
∃-¬Before x x₁ (x₂ ∷ b) (px ∷ u) x∈ with decp x₁ x₂
... | yes x₁≡x₂ = just g₁
  where g₁ : x before x₁ en (x₂ ∷ b) → ⊥
        g₁ ([] , ys , x₂∷b≡xs++x∷ys , x₁∈ys) with ∷-injectiveʳ x₂∷b≡xs++x∷ys
        ... | b≡ys = ¬≡-⊎->⇒¬≡ x₂ x₁ b px (subst (λ x₃ → x₁ P.∈ x₃) (sym b≡ys) x₁∈ys) (sym x₁≡x₂)
        g₁ (x₃ ∷ xs , ys , x₂∷b≡x₃∷xs++x∷ys , x₁∈ys) with  ∷-injectiveʳ x₂∷b≡x₃∷xs++x∷ys
        ... | b≡xs++x∷ys = ¬≡-⊎->⇒¬≡ x₂ x₁ b px (subst (λ x₄ → x₁ P.∈ x₄) (sym b≡xs++x∷ys) (∈-++⁺ʳ xs (there x₁∈ys))) (sym x₁≡x₂)
... | no ¬x₁≡x₂ with decp x x₂
... | yes x≡x₂ = nothing
... | no ¬x≡x₂ with ∃-¬Before x x₁ b u (tail ¬x≡x₂ x∈)
... | nothing = nothing
... | just ¬bf = just λ bf → ¬bf (g₁ bf)
  where g₁ : x before x₁ en (x₂ ∷ b) → x before x₁ en b
        g₁ ([] , ys , x₂∷b≡xs++x∷ys , x₁∈ys) = contradiction (sym (∷-injectiveˡ x₂∷b≡xs++x∷ys)) ¬x≡x₂
        g₁ (x ∷ xs , ys , x₂∷b≡xs++x∷ys , x₁∈ys) = xs , ys , ∷-injectiveʳ x₂∷b≡xs++x∷ys , x₁∈ys

∃Speculative2 : ∀ x₂ b ls rs → Unique-> (map proj₁ ls) → x₂ P.∈ (proj₁ b) → Maybe (∃[ x₁ ](∃[ v ](x₁ P.∈ (cmdsRun ls) × ¬ x₂ before x₁ en (proj₁ b) × v ∈ rs × v ∈ cmdWrote ls x₁)))
∃Speculative2 x₂ (b , _) [] rs u x₂∈b = nothing
∃Speculative2 x₂ (b , u1) (x ∷ ls) rs (px ∷ u) x₂∈b with ∃-¬Before x₂ (proj₁ x) b u1 x₂∈b
... | nothing with ∃Speculative2 x₂ (b , u1) ls rs u x₂∈b
... | nothing = nothing
... | just (x₁ , v , x₁∈ls , ¬bf , v∈rs , v∈ws)
  = just (x₁ , v , there x₁∈ls , ¬bf , v∈rs , ∈-cmdWrote∷ v x x₁ ls v∈ws (¬≡-⊎->⇒¬≡ (proj₁ x) x₁ (map proj₁ ls) px x₁∈ls))
∃Speculative2 x₂ b (x ∷ ls) rs (px ∷ u) x₂∈b | just ¬bf with ∃Intersection rs (cmdWrote (x ∷ ls) (proj₁ x))
... | just (v , v∈rs , v∈ws) = just (proj₁ x , v , here refl , ¬bf , v∈rs , v∈ws)
... | nothing with ∃Speculative2 x₂ b ls rs u x₂∈b
... | nothing = nothing
... | just (x₁ , v , x₁∈ls , ¬bf₁ , v∈rs , v∈ws)
  = just (x₁ , v , there x₁∈ls , ¬bf₁ , v∈rs
         , ∈-cmdWrote∷ v x x₁ ls v∈ws (¬≡-⊎->⇒¬≡ (proj₁ x) x₁ (map proj₁ ls) px x₁∈ls))

∃Speculative1 : ∀ (ls : FileInfo) (p : Unique-> (map proj₁ ls)) (b : ΣNBuild) (ran : NBuild) → Maybe (∃[ x₁ ](∃[ x₂ ](∃[ v ](x₂ before x₁ en (cmdsRun ls) × x₂ P.∈ (proj₁ b) × ¬ x₂ before x₁ en (proj₁ b) × v ∈ cmdRead ls x₂ × v ∈ cmdWrote ls x₁))))
∃Speculative1 [] _ b ran = nothing
∃Speculative1 (x ∷ ls) (px ∷ p) nb@(b , u) ran with required? (proj₁ x) b ((cmdsRun ls) ++ ran)
... | just x∈b with ∃Speculative2 (proj₁ x) nb ls (cmdRead (x ∷ ls) (proj₁ x)) p x∈b
... | just (x₁ , v , x₁∈ls , ¬bf , v∈rs , v∈ws)
  = just (x₁ , proj₁ x , v , ([] , cmdsRun ls , refl , x₁∈ls) , x∈b , ¬bf , v∈rs
         , ∈-cmdWrote∷ v x x₁ ls v∈ws (¬≡-⊎->⇒¬≡ (proj₁ x) x₁ (map proj₁ ls) px x₁∈ls))
... | nothing with ∃Speculative1 ls p nb ((proj₁ x) ∷ ran)
... | nothing = nothing
... | just (x₁ , x₂ , v , bf@(xs , ys , ≡₁ , x₁∈ys) , x₂∈b , ¬bf , v∈cr , v∈cw)
  = just (x₁ , x₂ , v , before-∷ x₂ x₁ (proj₁ x) (cmdsRun ls) bf , x₂∈b , ¬bf
         , ∈-cmdRead∷ v x x₂ ls v∈cr
           (¬≡-⊎->⇒¬≡ (proj₁ x) x₂ (map proj₁ ls) px (subst (λ x₃ → x₂ P.∈ x₃) (sym ≡₁) (∈-++⁺ʳ xs (here refl))))
         , ∈-cmdWrote∷ v x x₁ ls v∈cw
           (¬≡-⊎->⇒¬≡ (proj₁ x) x₁ (map proj₁ ls) px (subst (λ x₃ → x₁ P.∈ x₃) (sym ≡₁) (∈-++⁺ʳ xs (there x₁∈ys)))))
∃Speculative1 (x ∷ ls) (px ∷ p) nb@(b , u) ran | nothing with ∃Speculative1 ls p nb ((proj₁ x) ∷ ran)
... | nothing = nothing
... | just (x₁ , x₂ , v , bf@(xs , ys , ≡₁ , x₁∈ys) , x₂∈b , ¬bf , v∈cr , v∈cw)
  = just (x₁ , x₂ , v , before-∷ x₂ x₁ (proj₁ x) (cmdsRun ls) bf , x₂∈b , ¬bf
         , ∈-cmdRead∷ v x x₂ ls v∈cr
           (¬≡-⊎->⇒¬≡ (proj₁ x) x₂ (map proj₁ ls) px (subst (λ x₃ → x₂ P.∈ x₃) (sym ≡₁) (∈-++⁺ʳ xs (here refl))))
         , ∈-cmdWrote∷ v x x₁ ls v∈cw
           (¬≡-⊎->⇒¬≡ (proj₁ x) x₁ (map proj₁ ls) px (subst (λ x₃ → x₁ P.∈ x₃) (sym ≡₁) (∈-++⁺ʳ xs (there x₁∈ys)))))

∃Speculative : ∀ s x b ls → Maybe (Hazard s x b ls)
∃Speculative s x b ls with ∃Speculative1 (proj₁ (save x (cmdReads s x) (cmdWrites s x) ls))
                                         (proj₂ (save x (cmdReads s x) (cmdWrites s x) ls)) b []
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

checkHazard : ∀ s x b ls → Maybe (Hazard s x b ls)
checkHazard s x b ls with ∃WriteWrite s x b ls
... | just hz = just hz
... | nothing with ∃Speculative s x b ls
... | just hz = just hz
... | nothing = ∃ReadWrite s x b ls

doRunWError : ∀ b → (((s , mm) , ls) : State × ΣFileInfo) → (x : Cmd) → Hazard s x b ls ⊎ State × ΣFileInfo
doRunWError b ((s , mm) , ls) x with checkHazard s x b ls
... | just hz = inj₁ hz
... | nothing = let sys₁ = St.run oracle x s in
                inj₂ ((sys₁ , St.save x ((cmdReads s x) ++ (cmdWrites s x)) sys₁ mm)
                      , save x (cmdReads s x) (cmdWrites s x) ls)

run : State -> Cmd -> State
run st cmd = if (run? cmd st)
             then doRun st cmd
             else st

runWError : ∀ b → (((s , mm) , ls) : State × ΣFileInfo) → (x : Cmd) → Hazard s x b ls ⊎ State × ΣFileInfo
runWError b (st , ls) x with (run? x st)
... | true = doRunWError b (st , ls) x
... | false = inj₂ (st , ls)

exec : State -> Build -> State
exec st [] = st
exec st (x ∷ b) = exec (run st x) b

execWError : State × ΣFileInfo → (b₁ : Build) → (b₂ : ΣNBuild) → ∃[ s ](∃[ x ](∃[ ls ](Hazard s x b₂ ls))) ⊎ State × ΣFileInfo
execWError st [] b₂ = inj₂ st
execWError st (x ∷ b₁) b₂ with runWError b₂ st x
... | inj₁ hz = inj₁ (proj₁ (proj₁ st) , x , proj₂ st , hz)
... | inj₂ a = execWError a b₁ b₂

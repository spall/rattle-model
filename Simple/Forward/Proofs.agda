
module Forward.Proofs where

open import Agda.Builtin.Equality
open import File using (FileName ; Files ; fileNames)
open import Forward.System using (exec ; empty ; run ; Memory ; run?)

open import Build using (Build ; HazardFree ; writes)
open import Cmd using (Cmd ; outputFileNames ; outputs)
open import Data.Bool using (true ; false)
open import Data.List using ([] ; _∷_ ; foldr)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ ; ∈-++⁺ˡ)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.Product using (_,_ ; proj₁ ; _×_)
open import Data.String.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (trans ; sym)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import State using (State ; extend)


{- just like Cmd.lemma2 but we need to split on whether or not we will run the command 
   and we use proj₁ -}
lemma2 : (cmd : Cmd) -> (s : FileName) -> s Cmd.A.∉ (outputFileNames cmd) -> ∀ st-mm -> (proj₁ st-mm) s ≡ (proj₁ (run cmd st-mm)) s
lemma2 x s p = λ st-mm → f x st-mm p
  where g : (ls : Files) -> s Cmd.A.∉ fileNames ls -> ∀ st -> st s ≡ foldr extend st ls s
        g [] p = λ st → refl
        g ((s₁ , v₁) ∷ ls) p with s₁ ≟ s
        ... | yes s₁≡s = contradiction (here (sym s₁≡s)) p
        ... | no ¬s₁≡s = g ls λ x₁ → p (there x₁)
        f : (cmd : Cmd) -> ((st , mm) : (State × Memory)) -> s Cmd.A.∉ (outputFileNames cmd) -> (proj₁ (st , mm)) s ≡ proj₁ (run cmd (st , mm)) s
        f x (st , mm) p with run? x st mm
        ... | false = refl
        ... | true = g (outputs x) p st


{- just like Build.lemma1 but we use proj₁ -}
lemma1 : (s : FileName) -> (b : Build) -> s Cmd.A.∉ writes b -> ∀ st-mm -> (proj₁ st-mm) s ≡ proj₁ (exec st-mm b) s
lemma1 s [] p = λ st-mm → refl
lemma1 s (x ∷ b) p with (lemma1 s b λ x₁ → p (∈-++⁺ʳ (outputFileNames x) x₁)) | lemma2 x s λ x₁ → p (∈-++⁺ˡ x₁)
... | f | f₂ = λ st-mm → trans (f₂ st-mm) (f (run x st-mm))


idempotent-build : (b : Build) -> HazardFree b [] -> ∀ x st -> (proj₁ (exec (st , empty) b)) x ≡ (proj₁ (exec (exec (st , empty) b) b)) x
idempotent-build b p = λ x → f x
  where f : (x : FileName) -> ∀ st -> (proj₁ (exec (st , empty) b)) x ≡ (proj₁ (exec (exec (st , empty) b) b)) x
        f s with s Cmd.A.∈? writes b
        ... | yes x = {!!}
        ... | no ¬x = λ st → lemma1 s b ¬x (exec (st , empty) b)

{-
minimalist-build : 

unchanging-build :

reordered-build :

parallel-build :

additional-commands :

preservation-of-hazards :
-}

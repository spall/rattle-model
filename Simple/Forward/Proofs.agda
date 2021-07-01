
module Forward.Proofs where

open import Agda.Builtin.Equality
open import File using (FileName ; Files ; fileNames)
open import Forward.System as Sys using (exec ; empty ; run ; Memory ; run? ; [] ; Cons ; freshBuild ; changed? ; HazardFree)

open import Build using (Build ; writes ; Cons ; lemma2-3)
open import Cmd using (Cmd ; outputFileNames ; outputs)
open import Data.Bool using (true ; false)
open import Data.List using ([] ; _∷_ ; foldr ; List ; _++_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ ; ∈-++⁺ˡ)
open import Data.List.Membership.Setoid.Properties using (∈-++⁻) 
open import Data.List.Relation.Unary.Any using (here ; there ; tail)
open import Data.Product using (_,_ ; proj₁ ; _×_ ; ∃-syntax)
open import Data.String using (String)
open import Data.String.Properties using (_≟_ ; _==_ ; ≡-setoid)
open import Relation.Binary.PropositionalEquality using (trans ; sym ; inspect)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import State using (State ; extend)
open import Data.Maybe using (just ; nothing ; Maybe)
open import Data.Maybe.Relation.Binary.Pointwise using (dec)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Nullary.Decidable.Core using (isNo)

open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)


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
        f x (st , mm) p with isNo (dec _≡?_ (changed? st mm x) (just []))
        ... | false = refl
        ... | true = g (outputs x) p st


{- just like Build.lemma1 but we use proj₁ -}
lemma1 : (s : FileName) -> (b : Build) -> s Cmd.A.∉ writes b -> ∀ st-mm -> (proj₁ st-mm) s ≡ proj₁ (exec st-mm b) s
lemma1 s [] p = λ st-mm → refl
lemma1 s (x ∷ b) p with (lemma1 s b λ x₁ → p (∈-++⁺ʳ (outputFileNames x) x₁)) | lemma2 x s λ x₁ → p (∈-++⁺ˡ x₁)
... | f | f₂ = λ st-mm → trans (f₂ st-mm) (f (run x st-mm))


lemma4 : {ls₁ ls₂ : List FileName} {s : FileName} -> s Cmd.A.∉ ls₁ -> s Cmd.A.∈ ls₁ ++ ls₂ -> s Cmd.A.∈ ls₂
lemma4 {ls} p₁ p₂ with ∈-++⁻ ≡-setoid ls p₂
... | inj₁ x = contradiction x p₁
... | inj₂ y = y


{- need to prove that each command is going to run. 
   can do that by proving (mm cmd) ≡ nothing 
-}
lemma3-2 : {x : Maybe (List FileName)} -> x ≡ nothing -> isNo (dec _≡?_ x (just [])) ≡ true
lemma3-2 refl = refl


{- we are considering whether we should run the cmd; x. -}
{-
lemma3-3 : {st : State} {mm : Memory} (s : FileName) -> (x : Cmd) -> s Cmd.A.∈ outputFileNames x -> (changed? st mm x) ≡ nothing -> ∃[ v ](proj₁ (run x (st , mm)) s ≡ just v)
lemma3-3 {st} {mm} s x p₁ p₂ with lemma3-2 p₂ 
... | _ with run? st mm x
... | true with f (Cmd.outputs x) p₁
  where f : (ls : Files) -> s Cmd.A.∈ fileNames ls -> ∃[ v ](∀ st -> foldr extend st ls s ≡ just v)
        f ((s₁ , v₁) ∷ ls) p with s₁ ≟ s | inspect (_==_ s₁) s
        ... | yes s₁≡s | b = v₁ , λ st -> refl
        ... | no ¬s₁≡s | b = f ls (tail (λ s≡s₁ -> ¬s₁≡s (sym s≡s₁)) p)
... | v , f = v , f st
-}

{- this is true if:
   1. changed? x st mm == true or
   2. st s ≡ just v
-}
lemma3-3 : {st : State} {mm : Memory} {ls : List String} -> (s : FileName) -> (x : Cmd) -> s Cmd.A.∈ outputFileNames x -> ∃[ v ](proj₁ (run x (st , mm)) s ≡ just v)
lemma3-3 {st} {mm} s x p with run? st mm x
{- prove that st s ≡ just v
   how do we prove that?
   contradiction hopefully. 
  if run? st mm x ≡ false then there exists memory for the command; so it has run before. and
  its inputs haven't changed, but an output has, which means ∃[ cmd ]∃[ y ](run cmd s ≡ just y)
  but this is not possible because the build is hazard free.....

  I think I also need ot show that the command ran before in the build, which i should be able to do if i show we started with an empty memory? or 
-}
... | false = contradiction {!!} {!!} {- prove that st s ≡ just v -} 
... | true = {!!}



lemma3-1 : {st : State} {ls : List String} (s : FileName) -> (b : Build) -> s Cmd.A.∈ writes b -> HazardFree b ls -> ∃[ v ](proj₁ (exec (st , empty) b) s ≡ just v)
lemma3-1 s (x ∷ b) p p₁ = {!!}
  where f : {st : State} {mm : Memory} {ls : List String} (s : FileName) -> (b : Build) -> s Cmd.A.∈ writes b -> HazardFree b ls -> ∃[ v ](proj₁ (exec (st , mm) b) s ≡ just v)
        f s (x ∷ b) p p₁ with s Cmd.A.∈? outputFileNames x
{- just need to prove that (run x st mm) ≡ just v -}
        ... | yes p₂ = {!!}
        ... | no ¬p₂ = {!!}


{-
lemma3-1 : {st : State} {mm : Memory} {ls : List String} (s : FileName) -> (b : Build) -> HazardFree b ls -> s Cmd.A.∈ writes b -> freshBuild b st mm -> ∃[ v ](proj₁ (exec (st , mm) b) s ≡ just v)
lemma3-1 {st} {mm} s (x ∷ b) (Cons .x .b ls x₂ x₃ p₁) p₂ (Cons .x .b x₁ p₃) with s Cmd.A.∈? outputFileNames x
... | yes p with lemma3-3 {st} {mm} s x p x₁ | lemma1 s b (lemma2-3 s b (∈-++⁺ˡ p) p₁)
... | v , a | a₁ = v , trans (sym (a₁ (run x (st , mm)))) a
lemma3-1 {st} {mm} s (x ∷ b) (Cons .x .b ls x₂ x₃ p₁) p₂ (Cons .x .b x₁ p₃) | no ¬p with lemma3-2 x₁
... | _ with run? st mm x
... | true = lemma3-1 {Cmd.run x st} {Sys.extend x (Cmd.run x st) mm} s b p₁ (lemma4 ¬p p₂) p₃
-}


{- trying to prove:
   1. when we execute the build, if s ∈ writes build then state s ≡ value of s after build completes. where the build only tracks inputs, this is only true, all the time, if 
     a. the command executes; and the command only executes if either: an input has changed; or there is no memory of the cmd.
      
   2. What about builds where the same command appears 2x? 
      theoretically its ok because the memory should say that the command already ran so it wont run it again
      It shouldn't run it again because the build should be hazard free, so the input values shouldn't have changed during the run. 
      It is also possible that the hazard free requirement will prevent repeat commands, except in the case where the command doesnt write to anything?   I'm not sure what to do about this.  Maybe the hazardfree property should be refined? 

      
-}


lemma3 : (s : FileName) -> (b : Build) -> HazardFree b [] -> s Cmd.A.∈ writes b -> ∀ st -> proj₁ (exec (st , empty) b) s ≡ proj₁ (exec (exec (st , empty) b) b) s
lemma3 s b p₁ p₂ = {!!}



idempotent-build : (b : Build) -> HazardFree b [] -> ∀ x st -> (proj₁ (exec (st , empty) b)) x ≡ (proj₁ (exec (exec (st , empty) b) b)) x
idempotent-build b p = λ x → f x
  where f : (x : FileName) -> ∀ st -> (proj₁ (exec (st , empty) b)) x ≡ (proj₁ (exec (exec (st , empty) b) b)) x
        f s with s Cmd.A.∈? writes b
        ... | yes x = lemma3 s b p x
        ... | no ¬x = λ st → lemma1 s b ¬x (exec (st , empty) b)


{-
minimalist-build : 

unchanging-build :

reordered-build :

parallel-build :

additional-commands :

preservation-of-hazards :
-}

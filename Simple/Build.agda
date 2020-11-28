
module Build where

open import Agda.Builtin.Equality
open import Cmd using (Cmd ; DisjointFiles ; outputFileNames ; inputFileNames ; run ; lemma2)
open import Data.List using (List ; _++_ ; foldr ; [] ; _∷_)
open import Data.List.Membership.DecSetoid as ListMemDS
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Data.List.Membership.Setoid.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (tail)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.Maybe using (just)
open import Data.Product using (_,_ ; ∃-syntax ; _×_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-decSetoid ; _×ₛ_ ; ×-decidable)
open import Data.String using (String ; _≟_ ; _==_)
open import Data.String.Properties using (≡-decSetoid ; ≡-setoid)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import File using (FileName ; Files ; fileNames)
open import Relation.Binary.PropositionalEquality using (trans ; inspect ; sym)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import State using (State ; extend)

module D = ListMemDS (×-decSetoid ≡-decSetoid ≡-decSetoid)
open D using (_∈?_)

data Build : Set where
  []   : Build
  _::_ : Cmd -> Build -> Build

data HazardFree : Build -> List String -> Set where
  Null : {l : List String} -> HazardFree [] l -- empty build writes to nothing
  Cons : (c : Cmd) -> (b : Build) -> (l : List FileName) -> DisjointFiles c -> Disjoint (outputFileNames c) l -> HazardFree b ((outputFileNames c) ++ (inputFileNames c) ++ l) -> HazardFree (c :: b) l

exec : State -> Build -> State
exec st [] = st
exec st (x :: xs) = exec (run x st) xs

writes : Build -> List FileName
writes [] = []
writes (x :: b) = (outputFileNames x) ++ writes b

writesP : Build -> Files
writesP [] = []
writesP (x :: b) = (Cmd.outputs x) ++ writesP b

{- 
  st s ≡ run x st s
-}
buildLemma1 : (st : State) -> (s : FileName) -> (b : Build) -> s Cmd.A.∉ (writes b) -> st s ≡ (exec st b) s
buildLemma1 st s [] p = refl
buildLemma1 st s (x :: b) p
  = trans (lemma2 x s (λ a -> p (∈-++⁺ˡ a)))
          (buildLemma1 (run x st) s b (λ a -> p (∈-++⁺ʳ (outputFileNames x) a)))
          

buildLemma2-4 : {ls : List String} -> (s : FileName) -> (b : Build) -> s Cmd.A.∈ ls -> HazardFree b ls -> s Cmd.A.∉ writes b
buildLemma2-4 s .[] p2 Null = λ ()
buildLemma2-4 s .(c :: b) p2 (Cons c b ls _ x₁ p) with s Cmd.A.∈? outputFileNames c
... | yes p1 = λ x₂ → x₁ (p1 , p2)
... | no ¬p1 with buildLemma2-4 s b (∈-++⁺ʳ (outputFileNames c) (∈-++⁺ʳ (inputFileNames c) p2)) p
... | a = λ x₂ → a (f c b x₂ ¬p1)
  where f : (c : Cmd) -> (b : Build) -> s Cmd.A.∈ outputFileNames c ++ writes b -> s Cmd.A.∉ outputFileNames c -> s Cmd.A.∈ writes b
        f c b p p2 with ∈-++⁻ ≡-setoid (outputFileNames c) p
        ... | inj₁ i₁ = contradiction i₁ p2
        ... | inj₂ i₂ = i₂


buildLemma2-2 : {st : State} {st2 : State} -> (s : FileName) -> (x : Cmd) -> s Cmd.A.∈ outputFileNames x -> ∃[ v ](run x st s ≡ just v × run x st2 s ≡ just v)
buildLemma2-2 s x p = f (Cmd.outputs x) p
  where f : {st : State} {st2 : State} (ls : Files) -> s Cmd.A.∈ fileNames ls -> ∃[ v ](foldr extend st ls s ≡ just v × foldr extend st2 ls s ≡ just v)
        f ((s₁ , v₁) ∷ ls) p with s₁ ≟ s | inspect (_==_ s₁) s
        ... | yes s₁≡s | b = v₁ , (refl , refl)
        ... | no ¬s₁≡s | b = f ls (tail (λ s≡s₁ → ¬s₁≡s (sym s≡s₁)) p)


buildLemma2-3 : {st : State} (s : FileName) -> (b : Build) -> s Cmd.A.∉ writes b -> exec st b s ≡ st s
buildLemma2-3 s [] p = refl
buildLemma2-3 {st} s (x :: b) p = trans (buildLemma2-3 {run x st} s b λ x₁ → p (∈-++⁺ʳ (outputFileNames x) x₁))
                                        (sym (lemma2 x s λ x₁ → p (∈-++⁺ˡ x₁)))


buildLemma2-1 : {st : State} {st2 : State} {ls : List String} (s : FileName) -> (b : Build) -> HazardFree b ls -> s Cmd.A.∈ writes b -> ∃[ v ](exec st b s ≡ just v × exec st2 b s ≡ just v)
buildLemma2-1 {st} {st2} s (x :: b) p1 p2 with s Cmd.A.∈? outputFileNames x
... | yes p₁ with buildLemma2-2 {st} {st2} s x p₁  
buildLemma2-1 {st} {st2} s (x :: b) (Cons .x .b ls x₁ x₂ p1) p2 | yes p₁ | v , fst , snd
  = v , (trans (buildLemma2-3 {run x st} s b (buildLemma2-4 s b (∈-++⁺ˡ p₁) p1)) fst
        , trans (buildLemma2-3 {run x st2} s b (buildLemma2-4 s b (∈-++⁺ˡ p₁) p1)) snd) 
buildLemma2-1 {st} {st2} s (x :: b) (Cons .x .b ls x₁ x₂ p1) p2 | no ¬p₁ with ∈-++⁻ ≡-setoid (outputFileNames x) p2
... | inj₁ x₃ = contradiction x₃ ¬p₁
... | inj₂ y = buildLemma2-1 {run x st} {run x st2} s b p1 y


buildLemma2 : {st : State} -> (s : FileName) -> (b : Build) -> HazardFree b [] -> s Cmd.A.∈ (writes b) -> (exec st b) s ≡ (exec (exec st b) b) s
buildLemma2 {st} s b p1 p2 with buildLemma2-1 {st} {exec st b} s b p1 p2
... | v , fst , snd = trans fst (sym snd)


{- build is idempotent -}
build-idempotent : {st : State} -> (b : Build) -> HazardFree b [] -> ∀ x -> (exec st b) x ≡ (exec (exec st b) b) x
build-idempotent b p = λ x -> helper x
  where helper : {st : State} (s : FileName) -> (exec st b) s ≡ (exec (exec st b) b) s
        helper {st} s with s Cmd.A.∈? writes b
        ... | yes x = buildLemma2 s b p x
        ... | no x = buildLemma1 (exec st b) s b x

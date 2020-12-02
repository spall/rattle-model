
module Build where

open import Agda.Builtin.Equality
open import Cmd using (Cmd ; DisjointFiles ; outputFileNames ; inputFileNames ; run) renaming (lemma2 to Cmd-lemma2)
open import Data.List using (List ; _++_ ; foldr ; [] ; _∷_ ; foldl)
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
open import Relation.Binary.PropositionalEquality using (trans ; inspect ; sym ; subst ; subst₂)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import State using (State ; extend)

open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_ ; ↭-trans ; ↭-sym )
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (++⁺ˡ ; shifts ; ∈-resp-↭)
open import Data.List.Relation.Binary.Pointwise using (_∷_ ; Pointwise-≡⇒≡)

module D = ListMemDS (×-decSetoid ≡-decSetoid ≡-decSetoid)
open D using (_∈?_)


Build : Set
Build = List Cmd

data HazardFree : Build -> List String -> Set where
  Null : {l : List String} -> HazardFree [] l -- empty build writes to nothing
  Cons : (c : Cmd) -> (b : Build) -> (l : List FileName) -> DisjointFiles c -> Disjoint (outputFileNames c) l -> HazardFree b ((outputFileNames c) ++ (inputFileNames c) ++ l) -> HazardFree (c ∷ b) l


exec : State -> Build -> State
exec st [] = st
exec st (x ∷ xs) = exec (run x st) xs

writes : Build -> List FileName
writes [] = []
writes (x ∷ b) = (outputFileNames x) ++ writes b


lemma1 : (s : FileName) -> (b : Build) -> s Cmd.A.∉ writes b -> ∀ st -> st s ≡ exec st b s
lemma1 s [] p = λ st → refl
lemma1 s (x ∷ b) p with lemma1 s b (λ x₁ -> p (∈-++⁺ʳ (outputFileNames x) x₁)) | Cmd-lemma2 x s λ x₁ -> p (∈-++⁺ˡ x₁)
... | f | f₂ = λ st → trans (f₂ st) (f (run x st))
          

lemma2-3 : {ls : List String} -> (s : FileName) -> (b : Build) -> s Cmd.A.∈ ls -> HazardFree b ls -> s Cmd.A.∉ writes b
lemma2-3 s .[] p2 Null = λ ()
lemma2-3 s .(c ∷ b) p2 (Cons c b ls _ x₁ p) with s Cmd.A.∈? outputFileNames c
... | yes p1 = λ x₂ → x₁ (p1 , p2)
... | no ¬p1 with lemma2-3 s b (∈-++⁺ʳ (outputFileNames c) (∈-++⁺ʳ (inputFileNames c) p2)) p
... | a = λ x₂ → a (f c b x₂ ¬p1)
  where f : (c : Cmd) -> (b : Build) -> s Cmd.A.∈ outputFileNames c ++ writes b -> s Cmd.A.∉ outputFileNames c -> s Cmd.A.∈ writes b
        f c b p p2 with ∈-++⁻ ≡-setoid (outputFileNames c) p
        ... | inj₁ i₁ = contradiction i₁ p2
        ... | inj₂ i₂ = i₂


lemma2-2 : (s : FileName) -> (x : Cmd) -> s Cmd.A.∈ outputFileNames x -> ∃[ v ](∀ st -> run x st s ≡ just v)
lemma2-2 s x p = f (Cmd.outputs x) p
  where f : (ls : Files) -> s Cmd.A.∈ fileNames ls -> ∃[ v ](∀ st -> foldr extend st ls s ≡ just v)
        f ((s₁ , v₁) ∷ ls) p with s₁ ≟ s | inspect (_==_ s₁) s
        ... | yes s₁≡s | b = v₁ , λ st → refl
        ... | no ¬s₁≡s | b = f ls (tail (λ s≡s₁ → ¬s₁≡s (sym s≡s₁)) p)


lemma2-1 : {ls : List String} (s : FileName) -> (b : Build) -> HazardFree b ls -> s Cmd.A.∈ writes b -> ∃[ v ](∀ st -> exec st b s ≡ just v)
lemma2-1 s (x ∷ b) (Cons .x .b _ x₁ x₂ p₁) p₂ with s Cmd.A.∈? outputFileNames x
... | yes p with lemma2-2 s x p
... | v , f with lemma1 s b (lemma2-3 s b (∈-++⁺ˡ p) p₁)
... | f₁ = v , λ st → trans (sym (f₁ (run x st))) (f st)
lemma2-1 s (x ∷ b) (Cons .x .b _ x₁ x₂ p₁) p₂ | no ¬p with ∈-++⁻ ≡-setoid (outputFileNames x) p₂
... | inj₁ y = contradiction y ¬p
... | inj₂ y with lemma2-1 s b p₁ y
... | v , f = v , λ st → f (run x st)


lemma2 : (s : FileName) -> (b : Build) -> HazardFree b [] -> s Cmd.A.∈ writes b -> ∀ st -> exec st b s ≡ exec (exec st b) b s
lemma2 s b p₁ p₂ with lemma2-1 s b p₁ p₂
... | v , f = λ st → trans (f st) (sym (f (exec st b)))


{- build is idempotent -}
build-idempotent : (b : Build) -> HazardFree b [] -> ∀ x st -> (exec st b) x ≡ (exec (exec st b) b) x
build-idempotent b p = λ x -> helper x
  where helper : (s : FileName) -> ∀ st -> (exec st b) s ≡ (exec (exec st b) b) s
        helper s with s Cmd.A.∈? writes b
        ... | yes x = lemma2 s b p x
        ... | no x = λ st → lemma1 s b x (exec st b)

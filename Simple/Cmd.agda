
module Cmd where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Data.Bool.Base using (Bool)
open import Data.List using (foldr)
open import Data.List.Membership.DecSetoid as ListMemDS hiding (_∈_ ; _∈?_ ; _∉_)
open import Data.List.Membership.Setoid as ListMemS hiding (_∈_ ; _∉_)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Relation.Binary.Equality.DecPropositional as ListEqDp hiding (_≡?_)
open import Data.List.Relation.Unary.Any using (here ; there ; tail)
open import Data.Maybe using (just)
open import Data.Product using (_,_ ; ∃-syntax ; _×_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_ ; ×-decidable ; ≡×≡⇒≡ ; ≡⇒≡×≡)
open import Data.String using (String)
open import Data.String.Properties using (_≟_ ; ≡-setoid)
open import File using (Files ; FileName ; fileNames)
open import Function using (_∘₂_)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (trans ; sym ; decSetoid)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Nullary.Decidable.Core using (map′ ; isYes)
open import Relation.Nullary.Negation using (contradiction)
open import State using (State ; extend)

module A = ListMemDS (decSetoid _≟_)
open A using (_∈?_ ; _∉_)

module B = ListMemS (≡-setoid ×ₛ ≡-setoid)
open B using (_∈_)

{- decidable list of (string × string) -}
module C = ListEqDp ((map′ ≡×≡⇒≡ ≡⇒≡×≡) ∘₂ (×-decidable _≟_ _≟_))
open C using (_≡?_)

module D = ListEqDp _≟_
open D using (_≡?_)

{- first is inputs; 2nd is outputs -}
Cmd : Set
Cmd = (List FileName × Files)

_Cmd-≟_ : Decidable _≡_
_Cmd-≟_ = (map′ ≡×≡⇒≡ ≡⇒≡×≡) ∘₂ (×-decidable D._≡?_ C._≡?_)

_==_ : Cmd -> Cmd -> Bool
c₁ == c₂ = isYes (c₁ Cmd-≟ c₂)

inputs : Cmd -> List FileName
inputs = proj₁

outputs : Cmd -> Files
outputs = proj₂

outputFileNames : Cmd -> List FileName
outputFileNames cmd = fileNames (outputs cmd)

inputFileNames : Cmd  -> List FileName
inputFileNames = inputs

DisjointFiles : Cmd -> Set
DisjointFiles cmd = Disjoint (inputFileNames cmd) (outputFileNames cmd)

run : Cmd -> State -> State
run cmd st = foldr extend st (outputs cmd)

-- proofs about commands

{- If s ∉ outputs of cmd then the value of s in the state is the same before and after the command is run -}
lemma2 : (cmd : Cmd) -> (s : FileName) -> s ∉ (outputFileNames cmd) -> ∀ st -> st s ≡ run cmd st s
lemma2 cmd s = f (outputs cmd)
  where f : (ls : Files) -> s ∉ fileNames ls -> ∀ st -> st s ≡ foldr extend st ls s
        f [] p = λ st → refl
        f ((s₁ , v₁) ∷ ls) p with s₁ ≟ s
        ... | yes s₁≡s = contradiction (here (sym s₁≡s)) p
        ... | no ¬s₁≡s = f ls λ x → p (there x)


lemma1-1 : (s : FileName) -> (ls : Files) -> s A.∈ fileNames ls -> ∃[ v ](∀ st -> foldr extend st ls s ≡ just v)
lemma1-1 s ((s₁ , v₁) ∷ ls) p with s₁ ≟ s
... | yes p₁ = v₁ , λ st → refl
... | no ¬p₁ = lemma1-1 s ls (tail (λ x → ¬p₁ (sym x)) p)


lemma1 : (s : FileName) -> (x : Cmd) -> s A.∈ outputFileNames x -> ∀ st -> run x st s ≡ run x (run x st) s
lemma1 s x p with lemma1-1 s (outputs x) p
... | v , f = λ st → trans (f st) (sym (f (run x st)))


{- Proof a command is idempotent when run in any state -}
cmd-idempotent : (cmd : Cmd) -> ∀ s st -> (run cmd st) s ≡ run cmd (run cmd st) s
cmd-idempotent cmd = λ s -> helper s
  where helper : (s : String) -> ∀ st -> run cmd st s  ≡ run cmd (run cmd st) s
        helper s with s ∈? (outputFileNames cmd)
        ... | no x = λ st → (lemma2 cmd s x) (run cmd st)
        ... | yes x = lemma1 s cmd x

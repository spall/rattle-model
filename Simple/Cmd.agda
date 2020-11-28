
module Cmd where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Data.List using (foldr)
open import Data.List.Membership.DecSetoid as ListMemDS hiding (_∈_ ; _∈?_ ; _∉_)
open import Data.List.Membership.Setoid as ListMemS hiding (_∈_ ; _∉_)
open import Data.List.Relation.Unary.Any using (here ; there ; tail)
open import Data.Maybe using (just)
open import Data.Product using (_,_ ; proj₁; ∃-syntax ; _×_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.String using (String)
open import Data.String.Properties using (_≟_ ; ≡-setoid ; _==_)
open import File using (File ; Files ; FileName ; fileNames ; UniqueFiles ; Empty ; Cons)
open import Relation.Binary.PropositionalEquality using (trans ; sym ; decSetoid ; cong ; subst ; inspect)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import State using (State ; extend)

module A = ListMemDS (decSetoid _≟_)
open A using (_∈?_ ; _∉_)

module B = ListMemS (≡-setoid ×ₛ ≡-setoid)
open B using (_∈_)


record Cmd : Set where
  field
    inputs : Files
    outputs : Files

outputFileNames : Cmd -> List FileName
outputFileNames cmd = fileNames (Cmd.outputs cmd)

inputFileNames : Cmd  -> List FileName
inputFileNames cmd = fileNames (Cmd.inputs cmd)

run : Cmd -> State -> State
run cmd st = foldr extend st (Cmd.outputs cmd)

-- proofs about commands


{- If s ∉ outputs of cmd then the value of s in the state is the same before and after the command is run -}
lemma2 : {st : State} -> (cmd : Cmd) -> (s : FileName) -> s ∉ (outputFileNames cmd) -> st s ≡ (run cmd st) s
lemma2 cmd s = helper (Cmd.outputs cmd)
  where helper : {st : State} (ls : Files) -> s ∉ (fileNames ls) -> st s ≡ (foldr extend st ls) s
        helper [] p2 = refl
        helper {st} ((k , v) ∷ ls) p2 with k ≟ s -- need evidence k is not s
        ... | yes k≡s = contradiction (here (sym k≡s)) p2 -- impossible
        ... | no ¬k≡s = helper ls λ x → p2 (there x)


lemma1-1 : {st : State} {st2 : State} (s : FileName) (ls : Files) -> s A.∈ fileNames ls -> ∃[ v ](foldr extend st ls s ≡ just v × foldr extend st2 ls s ≡ just v)
lemma1-1 s ((s₁ , v₁) ∷ ls) p with s₁ ≟ s | inspect (_==_ s₁) s
... | yes p₁ | b = v₁ , (refl , refl)
... | no ¬p₁ | b = lemma1-1 s ls (tail (λ x → ¬p₁ (sym x)) p)


lemma1 : {st : State} (s : FileName) -> (ls : Files) -> s A.∈ fileNames ls -> (foldr extend st ls) s ≡ (foldr extend (foldr extend st ls) ls) s
lemma1 {st} s ls p with lemma1-1 {st} {foldr extend st ls} s ls p
... | v , fst , snd = trans fst (sym snd)


{- Proof a command is idempotent when run in a given state -}
cmd-idempotent : {st : State} -> (cmd : Cmd) -> ∀ x -> ((run cmd st) x) ≡ (run cmd (run cmd st)) x
cmd-idempotent {st} cmd = λ z -> helper z
  where helper : {st : State} -> (z : String) -> (run cmd st) z  ≡ (run cmd (run cmd st)) z
        helper {st} z with z ∈? (outputFileNames cmd)
        ... | no x = lemma2 {(run cmd st)} cmd z x
        ... | yes x = lemma1 z (Cmd.outputs cmd) x

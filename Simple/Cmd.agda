
module Cmd where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Data.Bool
open import Data.Empty
open import Data.Maybe
open import Data.List
open import Data.List.Membership.DecSetoid as ListMem
open import Data.List.Membership.Setoid as ListMem_
open import Data.List.Membership.Setoid.Properties as A

open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties
open import Data.List.Relation.Unary.Any as B
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Binary.Disjoint.Setoid.Properties
open import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties hiding (refl ; trans)
open import Data.List.Relation.Binary.Sublist.Propositional as C hiding (Disjoint)
open import Data.Product
open import Data.Product.Properties 
open import Data.String
open import Data.String.Properties as PropStr
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable.Core
open import Relation.Nullary.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent

open import Data.List.Relation.Binary.Equality.DecSetoid
open import Data.List.Relation.Binary.Disjoint.Propositional

module StrListMem = ListMem (PropEq.decSetoid Data.String._≟_)
module PairListMem_ = ListMem_ (×-setoid ≡-setoid ≡-setoid)

open import File as F
open import State as S

record Cmd : Set where
  field
    inputs : F.Files
    outputs : F.Files

outputFileNames : Cmd -> List F.FileName
outputFileNames cmd = F.fileNames (Cmd.outputs cmd)

inputFileNames : Cmd  -> List F.FileName
inputFileNames cmd = F.fileNames (Cmd.inputs cmd)

DisjointFiles : Cmd -> Set
DisjointFiles cmd = Disjoint (inputFileNames cmd) (outputFileNames cmd)

run : Cmd -> S.State -> S.State
run cmd st = foldr S.extend st (Cmd.outputs cmd)

-- proofs about commands


{- If s ∉ outputs of cmd then the value of s in the state is the same before and after the command is run -}
lemma2 : {st : State} -> (cmd : Cmd) -> (s : FileName) -> s StrListMem_.∉ (outputFileNames cmd) -> st s ≡ (run cmd st) s
lemma2 cmd s = helper (Cmd.outputs cmd)
  where helper : {st : State} (ls : Files) -> s StrListMem_.∉ (F.fileNames ls) -> st s ≡ (foldr extend st ls) s
        helper [] p2 = refl
        helper {st} ((k , v) ∷ ls) p2 with k PropStr.≟ s -- need evidence k is not s
        ... | yes k≡s = contradiction (here (PropEq.sym k≡s)) p2 -- impossible
        ... | no ¬k≡s = helper ls λ x → p2 (there x)


{- (s,v) ∈ ls implies extending the state with ls then looking up s will give the value of just v -}
lemma1-1 : {st : State} -> ((s , v) : File) -> (ls : Files) -> UniqueFiles (F.fileNames ls) -> (s , v) PairListMem_.∈ ls -> (foldr extend st ls) s ≡ just v
lemma1-1 (s , v) ((k₁ , v₁) ∷ ls) p1 p2 with (k₁ PropStr.≟ s)
lemma1-1 (s , v) ((k₁ , v₁) ∷ ls) p1 (here (_ , v≡v₁)) | yes x
  = cong just (PropEq.sym v≡v₁)
lemma1-1 (s , v) ((k₁ , v₁) ∷ ls) p1 (here (s≡k₁ , _)) | no ¬k₁≡s
  = ⊥-elim (¬k₁≡s (PropEq.sym s≡k₁))
lemma1-1 (s , v) ((k₁ , v₁) ∷ ls) (Cons .k₁ _ k₁∉ls _) (there p2) | yes k₁≡s
  = ⊥-elim (k₁∉ls (subst (λ x₂ → x₂ StrListMem_.∈ (F.fileNames ls)) (PropEq.sym k₁≡s) (l0 p2)))
  where l0 : (s , v) PairListMem_.∈ ls -> s StrListMem_.∈ (F.fileNames ls)
        l0 = A.∈-map⁺ (≡-setoid ×ₛ ≡-setoid) ≡-setoid proj₁
lemma1-1 (s , v) ((k₁ , v₁) ∷ ls) (Cons .k₁ _ x₁ p1) (there p2) | no ¬k₁≡s
  = lemma1-1 (s , v) ls p1 p2
  

{- I think we might not need the evidence of uniqueness since we use foldr; but we do use it... -}
{- s ∈ outputs of cmd aka ls; loop over ls via ls2 until we find (s , v) ∈ ls2 -}
{- I feel like there should be a nicer way of doing this -}
lemma1 : (st : State) -> (s : FileName) -> (ls : Files) -> UniqueFiles (F.fileNames ls) -> (ls2 : Files) -> s StrListMem_.∈ (F.fileNames ls2)
  -> UniqueFiles (F.fileNames ls2) ->  ls2 C.⊆ ls -> (foldr extend st ls) s ≡ (foldr extend (foldr extend st ls) ls) s
lemma1 st s ls1 p2 ((k , v) ∷ ls3) p3 p4 p5 with (k PropStr.≟ s) | inspect (_==_ k) s
... | yes p | PropEq.[ b ]
  = subst (λ x → foldr extend st ls1 x ≡ foldr extend (foldr extend st ls1) ls1 x) p
          (trans (lemma1-1 (k , v) ls1 p2 (C.lookup p5 (here (refl , refl))))
                 (PropEq.sym (lemma1-1 {foldr extend st ls1} (k , v) ls1 p2 (C.lookup p5 (here (refl , refl))))))
lemma1 _ s _ _  ((k , v) ∷ ls3) (here s≡k) _ _ | no ¬p | PropEq.[ b ]
  = ⊥-elim (¬p (PropEq.sym s≡k))
lemma1 st s ls1 p2 ((k , v) ∷ ls3) (there p3) (Cons .k .(Data.List.map proj₁ ls3) x p4) p5 | no ¬p | PropEq.[ b ]
  = lemma1 st s ls1 p2 ls3 p3 p4 (∷ˡ⁻ p5)


{- Proof a command is idempotent when run in a given state; if its output files are unique 
   (aka a set) TODO: would be nice to replace this self defined 
   claim of uniqueness with one already implemented in Agda
-}
cmd-idempotent : {st : S.State} -> (cmd : Cmd) -> F.UniqueFiles (outputFileNames cmd) -> ∀ x -> ((run cmd st) x) ≡ (run cmd (run cmd st)) x
cmd-idempotent {st} cmd p = λ z -> helper z
  where helper : {st : S.State} -> (z : String) -> (run cmd st) z  ≡ (run cmd (run cmd st)) z
        helper {st} z with z StrListMem.∈? (outputFileNames cmd)
        ... | no x = lemma2 {(run cmd st)} cmd z x
        ... | yes x = lemma1 st z (Cmd.outputs cmd) p (Cmd.outputs cmd) x p (⊆-reflexive refl)


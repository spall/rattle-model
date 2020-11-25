
module Cmd where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Data.List using (foldr)
open import Data.List.Membership.DecSetoid as ListMemDS hiding (_∈_ ; _∈?_ ; _∉_)
open import Data.List.Membership.Setoid as ListMemS hiding (_∈_ ; _∉_)
open import Data.List.Membership.Setoid.Properties using (∈-map⁺)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties using (∷ˡ⁻)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_ ; lookup ; ⊆-reflexive)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.Maybe using (just)
open import Data.Product using (_,_ ; proj₁)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.String using (String)
open import Data.String.Properties using (_≟_ ; ≡-setoid ; _==_)
open import File using (File ; Files ; FileName ; fileNames ; UniqueFiles ; Empty ; Cons)
open import Relation.Binary.PropositionalEquality using (trans ; sym ; decSetoid ; cong ; subst ; inspect ; [_])
open import Relation.Nullary using (yes ; no)
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

DisjointFiles : Cmd -> Set
DisjointFiles cmd = Disjoint (inputFileNames cmd) (outputFileNames cmd)

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


{- (s,v) ∈ ls implies extending the state with ls then looking up s will give the value of just v -}
lemma1-1 : {st : State} -> ((s , v) : File) -> (ls : Files) -> UniqueFiles (fileNames ls) -> (s , v) B.∈ ls -> (foldr extend st ls) s ≡ just v
lemma1-1 (s , v) ((k₁ , v₁) ∷ ls) p1 p2 with (k₁ ≟ s)
lemma1-1 (s , v) ((k₁ , v₁) ∷ ls) p1 (here (_ , v≡v₁)) | yes x
  = cong just (sym v≡v₁)
lemma1-1 (s , v) ((k₁ , v₁) ∷ ls) p1 (here (s≡k₁ , _)) | no ¬k₁≡s
  = contradiction (sym s≡k₁) ¬k₁≡s
lemma1-1 (s , v) ((k₁ , v₁) ∷ ls) (Cons .k₁ _ k₁∉ls _) (there p2) | yes k₁≡s
  = contradiction (subst (λ x₂ → x₂ A.∈ (fileNames ls)) (sym k₁≡s) (l0 p2)) k₁∉ls
  where l0 : (s , v) ∈ ls -> s A.∈ (fileNames ls)
        l0 = ∈-map⁺ (≡-setoid ×ₛ ≡-setoid) ≡-setoid proj₁
lemma1-1 (s , v) ((k₁ , v₁) ∷ ls) (Cons .k₁ _ x₁ p1) (there p2) | no ¬k₁≡s
  = lemma1-1 (s , v) ls p1 p2
  

{- I think we might not need the evidence of uniqueness since we use foldr; but we do use it... -}
{- s ∈ outputs of cmd aka ls; loop over ls via ls2 until we find (s , v) ∈ ls2 -}
{- I feel like there should be a nicer way of doing this -}
lemma1 : (st : State) -> (s : FileName) -> (ls : Files) -> UniqueFiles (fileNames ls) -> (ls2 : Files) -> s A.∈ (fileNames ls2)
  -> UniqueFiles (fileNames ls2) ->  ls2 ⊆ ls -> (foldr extend st ls) s ≡ (foldr extend (foldr extend st ls) ls) s
lemma1 st s ls1 p2 ((k , v) ∷ ls3) p3 p4 p5 with (k ≟ s) | inspect (_==_ k) s
... | yes p | [ b ]
  = subst (λ x → foldr extend st ls1 x ≡ foldr extend (foldr extend st ls1) ls1 x) p
          (trans (lemma1-1 (k , v) ls1 p2 (lookup p5 (here (refl , refl))))
                 (sym (lemma1-1 {foldr extend st ls1} (k , v) ls1 p2 (lookup p5 (here (refl , refl))))))
lemma1 _ s _ _  ((k , v) ∷ ls3) (here s≡k) _ _ | no ¬s≡k | [ b ]
  = contradiction (sym s≡k) ¬s≡k
lemma1 st s ls1 p2 ((k , v) ∷ ls3) (there p3) (Cons .k .(Data.List.map proj₁ ls3) x p4) p5 | no ¬p | [ b ]
  = lemma1 st s ls1 p2 ls3 p3 p4 (∷ˡ⁻ p5)


{- Proof a command is idempotent when run in a given state; if its output files are unique 
   (aka a set) TODO: would be nice to replace this self defined 
   claim of uniqueness with one already implemented in Agda
-}
cmd-idempotent : {st : State} -> (cmd : Cmd) -> UniqueFiles (outputFileNames cmd) -> ∀ x -> ((run cmd st) x) ≡ (run cmd (run cmd st)) x
cmd-idempotent {st} cmd p = λ z -> helper z
  where helper : {st : State} -> (z : String) -> (run cmd st) z  ≡ (run cmd (run cmd st)) z
        helper {st} z with z ∈? (outputFileNames cmd)
        ... | no x = lemma2 {(run cmd st)} cmd z x
        ... | yes x = lemma1 st z (Cmd.outputs cmd) p (Cmd.outputs cmd) x p (⊆-reflexive refl)



module Cmd where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Data.Bool
open import Data.Empty
open import Data.Maybe
open import Data.List
open import Data.List.Membership.DecSetoid as ListMem
open import Data.List.Membership.Setoid as ListMem_
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Disjoint.Setoid.Properties
open import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties hiding (refl ; trans)
open import Data.List.Relation.Binary.Sublist.Propositional as C hiding (Disjoint)
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.Dependent as A hiding (refl)
open import Data.String
open import Data.String.Properties as PropStr
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial as B
open import Relation.Nullary

open import Data.List.Relation.Binary.Disjoint.Propositional

module StrListMem = ListMem (PropEq.decSetoid Data.String._≟_)
module PairListMem_ = ListMem_ (A.setoid ≡-setoid (B.indexedSetoid ≡-setoid))

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


-- proof k is not s given proof that the list containing k does not contain s.
-- todo: this seems like it could be a builtin too
lemma5 : (s : FileName) -> ((k , v) : File) -> (ls : Files) -> s StrListMem_.∉ (F.fileNames ((k , v) ∷ ls)) -> (k == s) ≡ false
lemma5 s (k , v) ls p with (PropStr._≟_ k s) -- decidable equality of strings
... | x with proof x -- proof k ≡ s
... | ofʸ p₁ = ⊥-elim (p (here (PropEq.sym p₁))) 
... | ofⁿ ¬p = refl


-- if s is not k then st s ≡ extend (k , v) st s
lemma4 : (s : FileName) -> ((k , v) : File) -> (k == s) ≡ false -> (st : State) -> st s ≡ (extend (k , v) st) s
lemma4 s (k , v) p st with (k == s)
... | false = refl


-- if s is not in the files (x :: xs) then s is not in the files of xs
-- todo: this seems like it could be a builtin too
lemma3 : (s : FileName) -> (x : File) -> (xs : Files) -> s StrListMem_.∉ (F.fileNames (x ∷ xs)) -> s StrListMem_.∉ (F.fileNames xs)
lemma3 s x [] p = λ ()
lemma3 s x (b ∷ ls) p = λ x₁ → p (there x₁)


-- If s is not in output files, then the value in st is same before cmd is run as it is after.
lemma2 : (cmd : Cmd) -> (st : State) -> (s : FileName) -> s StrListMem_.∉ (outputFileNames cmd) -> st s ≡ (run cmd st) s
lemma2 cmd st s p = lemma2_ st s (Cmd.outputs cmd) p
  where lemma2_ : (st : State) -> (s : FileName) -> (ls : Files) -> s StrListMem_.∉ (F.fileNames ls) -> st s ≡ (foldr extend st ls) s
        lemma2_ st s ls p with ls
        ... | [] = refl
        ... | (k , v) ∷ as with lemma2_ st s as (lemma3 s (k , v) as p) -- evidence st s ≡ state extended with everything in as
        ... | p2 with foldr extend st as
        ... | st2 with lemma4 s (k , v) (lemma5 s (k , v) as p) st2
        ... | p3 = trans p2 p3


-- if s is an input and the inputs and outputs are disjoint, then s is not an output.
-- todo: seems like this could be a builtin too
lemma1 : {cmd : Cmd} -> (s : FileName) -> s StrListMem_.∈ (inputFileNames cmd) -> DisjointFiles cmd -> s StrListMem_.∉ (outputFileNames cmd)
lemma1 {cmd} str p1 p2 = lemma1_ str (inputFileNames cmd) (outputFileNames cmd) p2 p1
  where lemma1_ : (s : String) -> (l1 : List String) -> (l2 : List String) -> Disjoint l1 l2 -> s StrListMem_.∈ l1 -> s StrListMem_.∉ l2
        lemma1_ s l1 [] p1 p2 = λ ()
        lemma1_ s l1 (x ∷ l2) p1 p2 with Disjoint⇒AllAll PropStr.≡-setoid p1 | p1 {s}
        ... | a | b = λ c -> b (p2 , c)


-- todo: seems like this could be a builtin too
lemma11 : (k : FileName) -> ((s , v) : File) -> (ls : Files) -> k ≡ s -> (s , v) PairListMem_.∈ ls -> k StrListMem_.∈ (F.fileNames ls)
lemma11 k (s , v) ((s1 , v1) ∷ ls) p1 (here (fst , snd)) = here (trans p1 fst)
lemma11 k (s , v) ((s1 , v1) ∷ ls) p1 (there p2) = there (lemma11 k (s , v) ls p1 p2)


-- would be nice to say there exists a (k, v) in ls s.t. k == s instead of explicitely being forced to specify it
lemma10 : (st : State) -> (s : FileName) -> ((k , v) : File) -> (ls : Files)
  -> UniqueFiles (F.fileNames ls) -> (k , v) PairListMem_.∈ ls -> (k == s) ≡ true -> (foldr extend st ls) s ≡ just v
lemma10 st s (k , v) ((k₁ , v₁) ∷ ls) (Cons k₁ ls_ x p1) p2 p3 with (k₁ PropStr.≟ s) -- hmm using k here instead of s doesnt reduce problem as much, wonder why
... | .true because ofʸ p with (k PropStr.≟ s) | p2  
... | .true because ofʸ p₁ | here (_ , v≡v1) = PropEq.cong just (PropEq.sym v≡v1)
... | .true because ofʸ p₁ | there b = ⊥-elim (x (lemma11 k₁ (k , v) ls (trans p (PropEq.sym p₁)) b))

lemma10 st s (k , v) ((k₁ , v₁) ∷ ls) (Cons k₁ ls_ x p1) (here (k≡k₁ , proj₄)) p3 | .false because ofⁿ ¬p with (k PropStr.≟ s)
... | .true because ofʸ p = ⊥-elim (¬p (trans (PropEq.sym k≡k₁) p))
lemma10 st s (k , v) ((k₁ , v₁) ∷ ls) (Cons k₁ ls_ x p1) (there p2) p3 | .false because ofⁿ ¬p = lemma10 st s (k , v) ls p1 p2 p3


-- TODO: I can probably get rid of this; seems like it should be a builtin
lemma13 : {k : String} -> {s : String} -> k ≡ s -> (k == s) ≡ true
lemma13 {k} {s} p with (k PropStr.≟ s)
... | .true because ofʸ p₁ = refl
... | .false because ofⁿ ¬p = ⊥-elim (¬p p)


lemma9 : (st : State) -> (s : FileName) -> (ls : Files) -> s StrListMem_.∈ (F.fileNames ls) -> UniqueFiles (F.fileNames ls) -> (ls2 : Files) -> s StrListMem_.∈ (F.fileNames ls2) -> UniqueFiles (F.fileNames ls2) ->  ls2 C.⊆ ls -> (foldr extend st ls) s ≡ (foldr extend (foldr extend st ls) ls) s
lemma9 st s ls1 p1 p2 ((k , v) ∷ ls3) p3 p4 p5 with (k PropStr.≟ s)
... | .true because ofʸ p with lemma10 st s (k , v) ls1 p2 (C.lookup p5 (here (refl , refl)))  (lemma13 p)
... | x with lemma10 (foldr extend st ls1) s (k , v) ls1 p2 (C.lookup p5 (here (refl , refl))) (lemma13 p)
... | y = trans x (PropEq.sym y)

lemma9 st s ls1 p1 p2 ((k , v) ∷ ls2) (here s≡k) p4 p5 | .false because ofⁿ ¬p = ⊥-elim (¬p (PropEq.sym s≡k))
lemma9 st s ls1 p1 p2 ((k , v) ∷ ls2) (there p3) (Cons .k ls_ x p4) p5 | .false because ofⁿ ¬p = lemma9 st s ls1 p1 p2 ls2 p3 p4 (∷ˡ⁻ p5)


lemma6 : (cmd : Cmd) -> (st : State) -> (s : FileName) -> s StrListMem_.∈ (outputFileNames cmd) -> UniqueFiles (outputFileNames cmd) -> (run cmd st) s ≡ (run cmd (run cmd st)) s
lemma6 cmd st s p p2 = lemma9 st s (Cmd.outputs cmd) p p2 (Cmd.outputs cmd) p p2 (⊆-reflexive refl)


{- 
-}
cmd-idempotent-helper : {cmd : Cmd} -> {st : S.State} -> Disjoint (inputFileNames cmd) (outputFileNames cmd) -> UniqueFiles (outputFileNames cmd) -> (z : String) -> (run cmd st) z ≡ (run cmd (run cmd st)) z
cmd-idempotent-helper {cmd} {st} p p2 z with z StrListMem.∈? (inputFileNames cmd)
... | yes x = lemma2 cmd (run cmd st) z (lemma1 {cmd} z x p) -- z is not in outputs because it is in inputs
... | no x with z StrListMem.∈? (outputFileNames cmd) -- z is not in inputs
... | no y = lemma2 cmd (run cmd st) z y -- z is not in outputs
... | yes y = lemma6 cmd st z y p2 -- z is in outputs


{- Proof a command is idempotent when run in a given state; if its input files and output files are disjoint
   and its output files are unique (aka a set) TODO: would be nice to replace this self defined 
   claim of uniqueness with one already implemented in Agda
-}
cmd-idempotent : {cmd : Cmd} -> {st : S.State} -> Disjoint (inputFileNames cmd) (outputFileNames cmd) -> F.UniqueFiles (outputFileNames cmd) -> ∀ x -> ((run cmd st) x) ≡ (run cmd (run cmd st)) x
cmd-idempotent {cmd} {st} p p2 = λ z -> cmd-idempotent-helper {cmd} {st} p p2 z


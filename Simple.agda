
module Simple where

open import Data.Maybe
open import Data.Nat
open import Data.Bool
open import Data.String
open import Data.String.Properties
open import Data.Product
open import Agda.Builtin.List
open import Data.List.Base
open import Data.List.Membership.DecSetoid as ListMem
open import Data.List.Membership.Setoid as ListMem_
open import Data.List.Relation.Binary.Disjoint.Setoid.Properties as DisjointProp
open import Data.List.Relation.Unary.All.Properties
open import Data.Empty
open import Relation.Nullary.Decidable.Core

open import Relation.Nullary
open import Relation.Nullary.Negation

open import Relation.Binary.PropositionalEquality as PropEq
open import Data.String.Properties as PropStr

open import Data.Product.Relation.Binary.Pointwise.Dependent as A hiding (refl)
open import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial as B

module StrListMem = ListMem (PropEq.decSetoid Data.String._≟_)

module StrListMem_ = ListMem_ ≡-setoid
module PairListMem_ = ListMem_ (A.setoid ≡-setoid (B.indexedSetoid ≡-setoid))


open import Data.List.Relation.Unary.All
open import Agda.Builtin.Equality
open import Data.List.Relation.Binary.Disjoint.Propositional
open import Function.Equality
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Equality.DecSetoid


Inputs : Set
Inputs = List (String × String)

Outputs : Set
Outputs = List (String × String)

record Cmd : Set where
  field
    inputs : Inputs
    outputs : Outputs

files : List (String × String) -> List String
files = Data.List.Base.map Data.Product.proj₁

-- k does not appear in ls. so elements of k :: ls are distinct
data UniqueFiles : List (String × String) -> Set where
  Empty : UniqueFiles []
  Cons : (k : String) -> (v : String) -> (ls : List (String × String)) -> k StrListMem_.∉ (files ls) -> UniqueFiles ls -> UniqueFiles ((k , v) ∷ ls)

outputFiles : Cmd -> List String
outputFiles cmd = files (Cmd.outputs cmd)

inputFiles : Cmd  -> List String
inputFiles cmd = files (Cmd.inputs cmd)

State : Set
State = String -> Maybe String

empty : State
empty x = nothing

--extend : State -> (String × String) -> State
extend : (String × String) -> State -> State
extend (k , v) st = \ k2 -> if (k == k2) then just v else st k2

data Build : Set where
  []   : Build
  _::_ : Cmd -> Build -> Build

run : Cmd -> State -> State
run cmd st = foldr extend st (Cmd.outputs cmd)

exec : State -> Build -> State
exec st [] = st
exec st (x :: xs) = exec (run x st) xs

-- proofs

-- if s is not in the files (x :: xs) then s is not in the files of xs
lemma3 : (s : String) -> (x : (String × String)) (xs : List (String × String)) -> s StrListMem_.∉ (files (x ∷ xs)) -> s StrListMem_.∉ (files xs)

lemma3 s x [] p = λ ()
lemma3 s x (b ∷ ls) p = λ x₁ → p (there x₁)

-- lemma10 : (s : String) -> ((k , v) : (String × String)) -> (ls : List (String × String)) -> s StrListMem_.∈ (

-- if s is not k then st s ≡ extend (k , v) st s
lemma4 : (s : String) -> ((k , v) : String × String) -> (k == s) ≡ false -> (st : State) -> st s ≡ (extend (k , v) st) s
lemma4 s (k , v) p st with (k == s)
... | false = refl

-- proof k is not s given proof that the list containing k does not contain s.
lemma5 : (s : String) -> ((k , v) : String × String) -> (ls : List (String × String)) -> s StrListMem_.∉ (files ((k , v) ∷ ls)) -> (k == s) ≡ false
lemma5 s (k , v) ls p with (PropStr._≟_ k s) -- decidable equality of strings
... | x with proof x -- proof k ≡ s
... | ofʸ p₁ = ⊥-elim (p (here (PropEq.sym p₁))) 
... | ofⁿ ¬p = refl

-- If s is not in output files, then the value in st is same before cmd is run as it is after.
lemma2 : (cmd : Cmd) -> (st : State) -> (s : String) -> s StrListMem_.∉ (files (Cmd.outputs cmd)) -> st s ≡ (run cmd st) s
lemma2 cmd st s p = lemma2_ st s (Cmd.outputs cmd) p
  where lemma2_ : (st : State) -> (s : String) -> (ls : List (String × String)) -> s StrListMem_.∉ (files ls) -> st s ≡ (foldr extend st ls) s
        lemma2_ st s ls p with ls
        ... | [] = refl
        ... | (k , v) ∷ as with lemma2_ st s as (lemma3 s (k , v) as p) -- evidence st s ≡ state extended with everything in as
        ... | p2 with foldr extend st as
        ... | st2 with lemma4 s (k , v) (lemma5 s (k , v) as p) st2
        ... | p3 = trans p2 p3

-- if s is an input and the inputs and outputs are disjoint, then s is not an output.
lemma1 : {cmd : Cmd} -> (s : String) -> s StrListMem_.∈ (inputFiles cmd) -> Disjoint (inputFiles cmd) (outputFiles cmd) -> s StrListMem_.∉ (outputFiles cmd)
lemma1 {cmd} str p1 p2 = lemma1_ str (inputFiles cmd) (outputFiles cmd) p2 p1
  where lemma1_ : (s : String) -> (l1 : List String) -> (l2 : List String) -> Disjoint l1 l2 -> s StrListMem_.∈ l1 -> s StrListMem_.∉ l2
        lemma1_ s l1 [] p1 p2 = λ ()
        lemma1_ s l1 (x ∷ l2) p1 p2 with Disjoint⇒AllAll PropStr.≡-setoid p1 | p1 {s}
        ... | a | b = λ c -> b (p2 , c)

-- prove k is s given proof that the list only containing k contains s.
lemma8 : (s : String) -> ((k , v) : String × String) -> s StrListMem_.∈ (files ((k , v) ∷ [])) -> (k == s) ≡ true
lemma8 s (k , v) (here px) with (PropStr._≟_ k s)
... | x with proof x
... | ofʸ p₁ = refl
... | ofⁿ ¬p = ⊥-elim (¬p (PropEq.sym px))


lemma11 : (k : String) -> ((s , v) : String × String) -> (ls : List (String × String)) -> k ≡ s -> (s , v) PairListMem_.∈ ls -> k StrListMem_.∈ (files ls)
lemma11 k (s , v) ((s1 , v1) ∷ ls) p1 (here (fst , snd)) = here (trans p1 fst)
lemma11 k (s , v) ((s1 , v1) ∷ ls) p1 (there p2) = there (lemma11 k (s , v) ls p1 p2)

lemma10 : (st : State) -> (s : String) -> ((k , v) : String × String) -> (ls : List (String × String))
  -> UniqueFiles ls -> (k , v) PairListMem_.∈ ls -> (k == s) ≡ true -> (foldr extend st ls) s ≡ just v
lemma10 st s (k , v) .((k₁ , v₁) ∷ ls) (Cons k₁ v₁ ls x p1) p2 p3 with (k₁ PropStr.≟ s) -- hmm using k here instead of s doesnt reduce problem as much, wonder why
... | .true because ofʸ p with (k PropStr.≟ s) | p2  
... | .true because ofʸ p₁ | here (_ , v≡v1) = PropEq.cong just (PropEq.sym v≡v1)
... | .true because ofʸ p₁ | there b = ⊥-elim (x (lemma11 k₁ (k , v) ls (trans p (PropEq.sym p₁)) b))

lemma10 st s (k , v) ((k₁ , v₁) ∷ ls) (Cons k₁ v₁ ls x p1) (here (k≡k₁ , proj₄)) p3 | .false because ofⁿ ¬p with (k PropStr.≟ s)
... | .true because ofʸ p = ⊥-elim (¬p (trans (PropEq.sym k≡k₁) p))
lemma10 st s (k , v) ((k₁ , v₁) ∷ ls) (Cons k₁ v₁ ls x p1) (there p2) p3 | .false because ofⁿ ¬p = lemma10 st s (k , v) ls p1 p2 p3

{-
lemma10 st s (k , v) .[] Empty () p3
lemma10 st s (k , v) ((k1 , v1) ∷ ls1) (Cons .k1 .v1 .ls1 x2 x3) p2 p3 with (PropStr._≟_ k1 s) | (PropStr._≟_ k s)
... | .true because ofʸ p | .true because ofʸ p₁ with trans p (PropEq.sym p₁)
lemma10 st s (k , v) ((k1 , v1) ∷ ls1) (Cons .k1 .v1 .ls1 x2 x3) (here (proj₃ , proj₄)) p3 | .true because ofʸ p | .true because ofʸ p₁ | b = PropEq.cong just (PropEq.sym proj₄)
lemma10 st s (k , v) ((k1 , v1) ∷ ls1) (Cons .k1 .v1 .ls1 x2 x3) (there p2) p3 | .true because ofʸ p | .true because ofʸ p₁ | b = ⊥-elim (x2 {!!}) -- lemma says p2 implies that goal.
lemma10 st s (k , v) ls (Cons k1 v1 ls1 x2 x3) p2 p3 | .false because ofⁿ ¬p | .true because ofʸ p = lemma10 st s (k , v) ls1 x3 {!!} {!!}
-}

lemma9 : (st : State) -> (s : String) -> (ls : List (String × String)) -> s StrListMem_.∈ (files ls) -> (foldr extend st ls) s ≡ (foldr extend (foldr extend st ls) ls) s
lemma9 st s ls p with foldr extend st ls
... | st2 = {!!}

-- step 1. since s is in ls....... that means there exists a (k , v) s.t k == s and
-- therefore, just v ≡ (foldr extend st ls) s

-- step 2. since s is in ls......... that means there exists a (k , v) s.t. k == s and
-- therefore, just v ≡ (foldr extend (foldr extend st ls) ls) s




-- we know that s is an output file, an we know (but no proof yet) that s only appears once in
-- output files.  

lemma6 : (cmd : Cmd) -> (st : State) -> (s : String) -> s StrListMem_.∈ (outputFiles cmd) -> (run cmd st) s ≡ (run cmd (run cmd st)) s
lemma6 cmd st s p = lemma9 st s (Cmd.outputs cmd) p

{-with (Cmd.outputs cmd)
... | (k , v) ∷ [] with extend (k , v) st | lemma8 s (k , v) p
... | st2 | p2 with (k == s)
... | true = refl
lemma6 cmd st s p | (k , v) ∷ x₁ ∷ ls with (k == s)
... | false = {!!}
... | true = {!!}
-}

-- restrict the state to just the inputs of the command?
-- tell lemma6 that z is not in inputs...
{-
  1. yes x; z is not in outputs therefore lemma2, where st = (run cmd st)
  2. no x; z is not in inputs, therefore it MIGHT be in the outputs
     -- 1. no y; z is not in outputs, therefore lemma2, where st = (run cmd st)
     -- 2. yes y; z is in outputs, therefore need to show same value is written to state both times
-}
cmd-idempotent-helper : {cmd : Cmd} -> {st : State} -> Disjoint (inputFiles cmd) (outputFiles cmd) -> (z : String) -> (run cmd st) z ≡ (run cmd (run cmd st)) z
cmd-idempotent-helper {cmd} {st} p z with z StrListMem.∈? (inputFiles cmd)
... | yes x = lemma2 cmd (run cmd st) z (lemma1 {cmd} z x p) -- z is not in outputs because it is in inputs
... | no x with z StrListMem.∈? (outputFiles cmd) -- z is not in inputs
... | no y = lemma2 cmd (run cmd st) z y -- z is not in outputs
... | yes y = lemma6 cmd st z y -- z is in outputs



{-
... | yes x with lemma1 {cmd} z x p | (run cmd st)
... | p2 | st2 with (run cmd st2)
... | st3 = {!!}

-- prove that each thing in outputfiles is added to st. when cmd is run.
-- prove that if s is not in the output files then its value in state before cmd is run is same
-- as after cmd is run


-- get evidence that z is not in outputs..... perform induction on that evidence; showing that we never add z to state.
-- if any element of outputs = z then bottom.
cmd-idempotent-helper {cmd} {st} p z | no x = {!!}
-}
cmd-idempotent : {cmd : Cmd} -> {st : State} -> Disjoint (inputFiles cmd) (outputFiles cmd) -> ∀ x -> ((run cmd st) x) ≡ (run cmd (run cmd st)) x
cmd-idempotent {cmd} {st} p = λ z -> cmd-idempotent-helper {cmd} {st} p z


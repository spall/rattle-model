
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

module StrListMem = ListMem (PropEq.decSetoid Data.String._≟_)
module StrListMem_ = ListMem_ (PropEq.setoid String)


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
lemma5 : (s : String) -> (x : (String × String)) (xs : List (String × String)) -> s StrListMem_.∉ (files (x ∷ xs)) -> s StrListMem_.∉ (files xs)
lemma5 s x [] p = λ ()
lemma5 s x (b ∷ ls) p = λ x₁ → p (there x₁)

-- if s is not k then st s ≡ extend (k , v) st s
lemma6 : (s : String) -> ((k , v) : String × String) -> (k == s) ≡ false -> (st : State) -> st s ≡ (extend (k , v) st) s
lemma6 s (k , v) p st with (k == s)
... | false = refl

-- proof k is not s given proof that the list containing k does not contain s.
lemma7 : (s : String) -> ((k , v) : String × String) -> (ls : List (String × String)) -> s StrListMem_.∉ (files ((k , v) ∷ ls)) -> (k == s) ≡ false
lemma7 s (k , v) ls p with (PropStr._≟_ k s) -- decidable equality of strings
... | x with proof x -- proof k ≡ s
... | ofʸ p₁ = ⊥-elim (p (here (PropEq.sym p₁)))
... | ofⁿ ¬p = refl

lemma4 : (st : State) -> (s : String) -> (ls : List (String × String)) -> s StrListMem_.∉ (files ls) -> st s ≡ (foldr extend st ls) s
lemma4 st s ls p with ls
... | [] = refl
... | (k , v) ∷ as with lemma4 st s as (lemma5 s (k , v) as p) -- evidence st s ≡ state extended with everything in as
... | p2 with foldr extend st as
... | st2 with lemma6 s (k , v) (lemma7 s (k , v) as p) st2
... | p3 = trans p2 p3

-- If s is not in output files, then the value in st is same before cmd is run as it is after.
lemma3 : (cmd : Cmd) -> (st : State) -> (s : String) -> s StrListMem_.∉ (files (Cmd.outputs cmd)) -> st s ≡ (run cmd st) s
lemma3 cmd st s p = lemma4 st s (Cmd.outputs cmd) p


lemma2 : (s : String) -> (l1 : List String) -> (l2 : List String) -> Disjoint l1 l2 -> s StrListMem_.∈ l1 -> s StrListMem_.∉ l2
lemma2 s l1 [] p1 p2 = λ ()
lemma2 s l1 (x ∷ l2) p1 p2 with Disjoint⇒AllAll PropStr.≡-setoid p1 | p1 {s}
... | a | b = λ c -> b (p2 , c)

lemma1 : {cmd : Cmd} -> (s : String) -> s StrListMem_.∈ (inputFiles cmd) -> Disjoint (inputFiles cmd) (outputFiles cmd) -> s StrListMem_.∉ (outputFiles cmd)
lemma1 {cmd} str p1 p2 = lemma2 str (inputFiles cmd) (outputFiles cmd) p2 p1

cmd-idempotent-helper : {cmd : Cmd} -> {st : State} -> Disjoint (inputFiles cmd) (outputFiles cmd) -> (z : String) -> (run cmd st) z ≡ (run cmd (run cmd st)) z
cmd-idempotent-helper {cmd} {st} p z with z StrListMem.∈? (inputFiles cmd)
... | yes x with lemma1 {cmd} z x p | (run cmd st)
... | a | st2 with (run cmd st2)
... | st3 = {!!}

-- prove that each thing in outputfiles is added to st. when cmd is run.
-- prove that if s is not in the output files then its value in state before cmd is run is same
-- as after cmd is run


-- get evidence that z is not in outputs..... perform induction on that evidence; showing that we never add z to state.
-- if any element of outputs = z then bottom.
cmd-idempotent-helper {cmd} {st} p z | no x = {!!}

cmd-idempotent : {cmd : Cmd} -> {st : State} -> Disjoint (inputFiles cmd) (outputFiles cmd) -> ∀ x -> ((run cmd st) x) ≡ (run cmd (run cmd st)) x
cmd-idempotent {cmd} {st} p = λ z -> cmd-idempotent-helper {cmd} {st} p z



open import Functional.State using (State ; Oracle ; Cmd ; FileSystem ; Memory ; extend) renaming (save to store)

module Functional.Forward.Exec (oracle : Oracle) where

open import Agda.Builtin.Equality
open import Functional.State.Helpers (oracle) as St using (cmdReadNames)
open import Data.Bool using (Bool ; if_then_else_)
open import Data.List using (List ; [] ; _∷_ ; map ; filter ; foldr ; _++_)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Data.Maybe as Maybe using (Maybe ; just ; decToMaybe ; is-nothing ; maybe ; nothing)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∃-syntax)
open import Function.Base using (_∘_)
open import Functional.File using (FileName ; FileContent ; Files)
open import Functional.Build (oracle) using (Build)
open import Relation.Nullary.Decidable.Core using (isNo)
open import Relation.Nullary.Negation using (¬?)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Data.List.Relation.Unary.All as All using (All ; all? ; lookup)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Relation.Binary.PropositionalEquality using (decSetoid ; trans ; sym ; subst ; cong)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Relation.Nullary using (yes ; no ; Dec)
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (Any-resp-⊆ ; ⊆-reflexive)

maybeAll : {sys : FileSystem} -> (ls : List (FileName × Maybe FileContent)) -> Maybe (All (λ (f₁ , v₁) → sys f₁ ≡ v₁) ls)
maybeAll {sys} ls = decToMaybe (g₁ ls)
  where g₁ : (ls : List (FileName × Maybe FileContent)) -> Dec (All (λ (f₁ , v₁) → sys f₁ ≡ v₁) ls)
        g₁ ls = all? (λ (f₁ , v₁) → ≡-dec _≟_ (sys f₁) v₁) ls

get : (x : Cmd) -> (ls : Memory) -> x ∈ map proj₁ ls -> List (FileName × Maybe FileContent)
get x ((x₁ , fs) ∷ ls) x∈ with x ≟ x₁
... | yes x≡x₁ = fs
... | no ¬x≡x₁ = get x ls (tail ¬x≡x₁ x∈)

run? : Cmd -> State -> Bool
run? x (s , m) with x ∈? map proj₁ m
... | no x∉ = Bool.true
... | yes x∈ = is-nothing (maybeAll {s} (get x m x∈))

-- store extends the Memory with a new entry
doRun : State -> Cmd -> State
doRun (s , m) x = let s₂ = St.run x s in
                   (s₂ , store x (cmdReadNames x s) s₂ m)

runF : Cmd → (FileSystem × Memory)
     → (FileSystem × Memory)
runF cmd st = if (run? cmd st)
               then doRun st cmd
               else st

fabricate : Build → (FileSystem × Memory)
          → (FileSystem × Memory)
fabricate [] st = st
fabricate (x ∷ b) st = fabricate b (runF x st)

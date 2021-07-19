
module Functional.Build where

open import Agda.Builtin.Nat using (suc ; zero) renaming (Nat to ℕ)
open import Data.List using (List ; [] ; _∷_)
open import Functional.State using (Cmd)
open import Data.Product using (_×_ ; _,_)
open import Data.Bool using (if_then_else_)
open import Data.String using (_==_)

Build : Set
Build = List Cmd

NBuild : Set
NBuild = List (Cmd × ℕ)

incr : Cmd → (Cmd → ℕ) → (Cmd → ℕ)
incr x₁ mp = \ x → if (x == x₁) then suc (mp x) else mp x

number : Build → NBuild
number = g₁ λ x → zero
  where g₁ : (Cmd → ℕ) → Build → NBuild
        g₁ mp [] = []
        g₁ mp (x ∷ b) = (x , mp x) ∷ g₁ (incr x mp) b
        

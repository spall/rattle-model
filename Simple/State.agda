
module State where

open import Data.Maybe
open import Data.Product
open import Data.Bool
open import Data.String.Properties

open import File as F

State : Set
State = F.FileName -> Maybe F.FileContent

empty : State
empty x = nothing

extend : F.File -> State -> State
extend (k , v) st = \ k2 -> if (k == k2) then just v else st k2

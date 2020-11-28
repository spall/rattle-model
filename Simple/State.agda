
module State where

open import Data.Bool using (if_then_else_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Product using (_,_)
open import Data.String.Properties using (_==_)
open import File using (File ; FileName ; FileContent)

State : Set
State = FileName -> Maybe FileContent

empty : State
empty x = nothing

extend : File -> State -> State
extend (k , v) st = \ k2 -> if (k == k2) then just v else st k2

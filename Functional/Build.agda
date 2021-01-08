
module Functional.Build where

open import Data.List using (List)
open import Functional.State using (Cmd)

Build : Set
Build = List Cmd

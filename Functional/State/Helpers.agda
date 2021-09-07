
open import Functional.State using (F ; Cmd ; System ; CmdProof ; CmdFunction ; extend)

module Functional.State.Helpers (oracle : F) where

open import Functional.File using (Files ; FileNames)
open import Data.Product using (map ; proj₁ ; proj₂ ; _×_)
open import Function using (_∘_ ; _∘₂_)
open import Data.List as L hiding (map)

-- commands for accessing State related data structures. In it's own file so we can parameterize
-- over F so each function doesn't need to take the oracle as an argument.

getNames : Files → FileNames
getNames = L.map proj₁

getCmdFunction : Cmd → CmdFunction
getCmdFunction = proj₁ ∘ oracle

cmdReads : Cmd → System → Files
cmdReads = proj₁ ∘₂ getCmdFunction

cmdWrites : Cmd → System → Files
cmdWrites = proj₂ ∘₂ getCmdFunction

cmdWriteNames : Cmd → System → FileNames
cmdWriteNames = getNames ∘₂ cmdWrites

cmdFiles : Cmd → System → Files × Files
cmdFiles = getCmdFunction

cmdReadNames : Cmd → System → FileNames
cmdReadNames = getNames ∘₂ cmdReads

cmdReadWriteNames : Cmd → System → FileNames
cmdReadWriteNames x s = (cmdReadNames x s) ++ (cmdWriteNames x s)

trace : Cmd → System → FileNames × FileNames
trace = (map getNames getNames) ∘₂ cmdFiles

run : Cmd → System → System
run x s = foldr extend s (cmdWrites x s)

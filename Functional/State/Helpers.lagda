
\begin{code}[hide]
open import Functional.State using (Oracle ; Cmd ; FileSystem ; CmdProof ; CmdFunction ; extend)

module Functional.State.Helpers (oracle : Oracle) where

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

cmdReads : Cmd → FileSystem → Files
cmdReads = proj₁ ∘₂ getCmdFunction

cmdWrites : Cmd → FileSystem → Files
cmdWrites = proj₂ ∘₂ getCmdFunction

cmdWriteNames : Cmd → FileSystem → FileNames
cmdWriteNames = getNames ∘₂ cmdWrites

cmdFiles : Cmd → FileSystem → Files × Files
cmdFiles = getCmdFunction

cmdReadNames : Cmd → FileSystem → FileNames
cmdReadNames = getNames ∘₂ cmdReads

cmdReadWriteNames : Cmd → FileSystem → FileNames
cmdReadWriteNames x s = (cmdReadNames x s) ++ (cmdWriteNames x s)

trace : Cmd → FileSystem → FileNames × FileNames
trace = (map getNames getNames) ∘₂ cmdFiles
\end{code}

\newcommand{\run}{%
\begin{code}
writes : Cmd → FileSystem → Files
writes = proj₂ ∘₂ getCmdFunction

run : Cmd → FileSystem → FileSystem
run x s = foldr extend s (writes x s)
\end{code}}

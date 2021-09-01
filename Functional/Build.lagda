
\begin{code}[hide]
module Functional.Build where

open import Data.List using (List)
open import Functional.State using (Cmd)
\end{code}

\newcommand{\build}{%
\begin{code}
Build : Set
Build = List Cmd
\end{code}}

\begin{code}[hide]
module Functional.File where

open import Data.List using (List)
open import Data.Product using (_×_)
open import Data.String using (String)
\end{code}

\newcommand{\filename}{%
\begin{code}
FileName : Set
FileName = String
\end{code}}

\newcommand{\filenames}{%
\begin{code}
FileNames : Set
FileNames = List FileName
\end{code}}

\newcommand{\filecontent}{%
\begin{code}
FileContent : Set
FileContent = String
\end{code}}

\newcommand{\file}{%
\begin{code}
File : Set
File = FileName × FileContent
\end{code}}

\newcommand{\files}{%
\begin{code}
Files : Set
Files = List File
\end{code}}

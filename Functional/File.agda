module Functional.File where

open import Data.List using (List)
open import Data.Product using (_×_)
open import Data.String using (String)

FileName : Set
FileName = String

FileNames : Set
FileNames = List FileName

FileContent : Set
FileContent = String

File : Set
File = FileName × FileContent

Files : Set
Files = List File

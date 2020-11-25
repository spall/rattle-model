
module File where

open import Data.List using (List ; map ; [] ; _∷_)
open import Data.List.Membership.Setoid as ListMemS hiding (_∉_)
open import Data.Product using (_×_)
open import Data.String using (String)
open import Data.String.Properties using (≡-setoid)

module StrListMemS = ListMemS ≡-setoid
open StrListMemS using (_∉_)

FileName : Set
FileName = String

FileContent : Set
FileContent = String

File : Set
File = FileName × FileContent

Files : Set
Files = List File

fileNames : Files -> List FileName
fileNames = map Data.Product.proj₁

-- k does not appear in ls. so elements of k :: ls are distinct
data UniqueFiles : List FileName -> Set where
  Empty : UniqueFiles []
  Cons : (k : FileName) -> (ls : List FileName) -> k ∉ ls -> UniqueFiles ls -> UniqueFiles (k ∷ ls)

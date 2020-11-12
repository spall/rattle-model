
module File where

open import Data.String
open import Data.String.Properties
open import Data.Product
open import Data.List
open import Data.List.Base

open import Data.List.Membership.Setoid as ListMem_
module StrListMem_ = ListMem_ ≡-setoid

FileName : Set
FileName = String

FileContent : Set
FileContent = String

File : Set
File = FileName × FileContent

Files : Set
Files = List File

fileNames : Files -> List FileName
fileNames = Data.List.Base.map Data.Product.proj₁

-- k does not appear in ls. so elements of k :: ls are distinct
data UniqueFiles : List FileName -> Set where
  Empty : UniqueFiles []
  Cons : (k : FileName) -> (ls : List FileName) -> k StrListMem_.∉ ls -> UniqueFiles ls -> UniqueFiles (k ∷ ls)


open import Functional.State as St using (State ; F ; Cmd ; System ; trace ; save ; Memory)

module Functional.Rattle.Exec (oracle : F) where

open import Data.Bool using (Bool ; if_then_else_ ; false ; true ; not)
open import Data.List using (List ; [] ; _∷_ ; map ; filter ; _++_ ; foldr ; all)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Maybe.Relation.Binary.Pointwise using (dec)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_)
open import Function.Base using (_∘_)
open import Functional.File using (FileName ; FileContent)
open import Functional.Build using (Build ; SBuild ; SCmd ; Speculative ; Required)
open import Relation.Nullary.Decidable.Core using (isYes)
open import Relation.Nullary.Negation using (¬?)
open import Functional.Forward.Exec (oracle) using (run?)
open import Functional.Rattle.Hazard using (Hazard ; SpeculativeWriteRead ; WriteWrite ; ReadWrite)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; map₂)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_ ; _∈_)
open import Relation.Nullary using (yes ; no)
open import Data.List.Relation.Unary.Any using (tail)

FileInfo : Set
FileInfo = List (Cmd × List FileName × List FileName)

doRun : State -> Cmd -> State
doRun (sys , mm) cmd = let sys₂ = St.run oracle cmd sys in
                           (sys₂ , save cmd ((proj₁ (trace oracle sys cmd)) ++ (proj₂ (trace oracle sys cmd))) sys₂ mm)

run : State -> Cmd -> State
run st cmd = if (run? cmd st)
             then doRun st cmd
             else st

{- do the writes of cmd intersect with files? -}
checkWritesIntersection : Cmd -> List FileName -> System -> Bool
checkWritesIntersection cmd files sys = g₁ (proj₂ (trace oracle sys cmd))
  where g₁ : List FileName -> Bool
        g₁ [] = false
        g₁ (x ∷ ws) with x ∈? files
        ... | yes x∈ = true
        ... | no x∉ = g₁ ws

{- did cmd write to something a cmd in the memory read? -}
checkReadWrite : Cmd -> System -> FileInfo -> Maybe Hazard
checkReadWrite cmd sys fileInfo
  = if checkWritesIntersection cmd (g₁ fileInfo) sys
    then just ReadWrite
    else nothing
    where g₁ : FileInfo -> List FileName
          g₁ = foldr (_++_ ∘ proj₁ ∘ proj₂) []

{- did cmd write to something a cmd in the memory wrote to? -}
checkWriteWrite : Cmd -> System -> FileInfo -> Maybe Hazard
checkWriteWrite cmd sys fileInfo
  = if checkWritesIntersection cmd (g₁ fileInfo) sys
    then just WriteWrite
    else nothing
    where g₁ : FileInfo -> List FileName
          g₁ = foldr (_++_ ∘ proj₂ ∘ proj₂) []


{- do all the cmds that come before this one in the build occur in the memory? -}
required? : (x : Cmd) -> Memory -> (b : Build) -> x ∈ b -> Bool
required? cmd mm rf cmd∈rf
  = let cmds = g₁ rf [] cmd∈rf in
        all (isYes ∘ (_∈? (map proj₁ mm))) cmds
    where g₁ : (b : Build) -> Build -> cmd ∈ b -> Build
          g₁ (x ∷ b) accu cmd∈b with cmd ≟ x
          ... | yes cmd≡x = accu
          ... | no ¬cmd≡x = g₁ b (x ∷ accu) (tail ¬cmd≡x cmd∈b)


{- is x₁ after x₂ in b? 
talking about first occurences -}
isAfter? : (b : Build) -> (x₁ : Cmd) -> x₁ ∈ b -> Cmd -> Bool
isAfter? b x₁ x∈b x₂ = g₁ b [] x∈b
  where g₁ : (b : Build) -> Build -> x₁ ∈ b -> Bool
        g₁ (x ∷ b) accu x₁∈b with x₁ ≟ x
        ... | yes x₁≡x = isYes (x₂ ∈? accu)
        ... | no ¬x₁≡x = g₁ b (x ∷ accu) (tail ¬x₁≡x x₁∈b)


{- find all cmds in memory that wrote to a file in the provided list -}
getWriters : List FileName -> FileInfo -> Build
getWriters fs [] = []
-- did x write to something in fs
getWriters fs ((x , _ , ws) ∷ mm) = if g₁ ws
                                    then x ∷ (getWriters fs mm)
                                    else getWriters fs mm
  where g₁ : List FileName -> Bool
        g₁ [] = false
        g₁ (x ∷ ls) with x ∈? fs
        ... | yes _ = true
        ... | no x∉ = g₁ ls


{- make sure all cmd's which wrote to a file this cmd read, have been required,
if cmd has been required -}
{- 1. check if cmd has been required; if not then return false
   2. find a list of cmds that write to a file cmd reads
   3. check that each of them is before cmd in the reference list. 
-}
checkWriteRead : State -> FileInfo -> Cmd -> Build -> Maybe Hazard
checkWriteRead (sys , mm) fi cmd rf with cmd ∈? rf
... | no cmd∉ = nothing
... | yes cmd∈ = if required? cmd mm rf cmd∈
                 then (let writers = getWriters (proj₁ (trace oracle sys cmd)) fi in -- get all of the cmds in memory that write to a file this cmd read
                          if all (isAfter? rf cmd cmd∈) writers
                          then nothing
                          else just SpeculativeWriteRead)
                 else nothing

hasHazard : State -> FileInfo -> Cmd -> Build -> Maybe Hazard
hasHazard st@(sys , mm) fi cmd rf with checkWriteRead st fi cmd rf
... | just hz = just hz
... | nothing with checkWriteWrite cmd sys fi
... | just hz = just hz
... | nothing = checkReadWrite cmd sys fi


doRunCheck : State -> FileInfo -> Cmd -> Build -> Hazard ⊎ (State × FileInfo)
doRunCheck st@(sys , mm) fi cmd rf with hasHazard st fi cmd rf
... | just hz = inj₁ hz
... | nothing = inj₂ ((doRun st cmd) , (cmd , proj₁ (trace oracle sys cmd) , proj₂ (trace oracle sys cmd)) ∷ fi)
    

{- 1. look for read/write hazards: did this command write to something a command in the memory read?

   2. look for write/write hazards: did this command write to something a command in the memory wrote?
   3. look for speculative write read hazards: make sure all cmds that wrote to something read by this command, occur before this cmd in the reference list.


but is it possible that by doing it this way we will discover some hazards earlier than we would in the real rattle? i think so

What does rattle do?  rattle speculates cmds and runs cmds from the real script in parallel.

which at the end, amounts to running the ocmmands in some order. when checking for hazards, 
a speculative write/read hazard occurs if the reader was required, and the writer was not required.

a command, x,  has NOT been required yet, if not all of the commands that occur before x in the 
reference list have run.  I think we can say a command has been required if all of the commands before it in the reference list have run? this seems safe enough although i know there is a "race" condition in real rattle. not sure if that matters.

-}

runWError : State -> FileInfo -> Cmd -> Build -> Hazard ⊎ (State × FileInfo)
runWError st@(sys , mm) fi cmd rf with run? cmd st
... | true = doRunCheck st fi cmd rf
... | false = inj₂ (st , fi)

exec : State -> Build -> State
exec st [] = st
exec st (x ∷ b) = exec (run st x) b

{-
execWError : System -> Build -> Build -> Hazard ⊎ State
execWError sys b rf with g₁ (sys , []) [] b rf
  where g₁ : State -> FileInfo -> Build -> Build -> Hazard ⊎ (State × FileInfo)
        g₁ st fi [] _ = inj₂ (st , fi)
        g₁ st fi (x ∷ b) rf with runWError st fi x rf
        ... | inj₁ hz  = inj₁ hz
        ... | inj₂ (st₂ , fi₂) = g₁ st₂ fi₂ b rf
... | inj₁ hz = inj₁ hz
... | inj₂ (st , _) = inj₂ st
-}

execWError : (State × FileInfo) -> Build -> Build -> Hazard ⊎ (State × FileInfo)
execWError stfi [] _ = inj₂ stfi
execWError (st , fi) (x ∷ b) rf with runWError st fi x rf
... | inj₁ hz = inj₁ hz
... | inj₂ stfi = execWError stfi b rf

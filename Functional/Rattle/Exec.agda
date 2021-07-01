{-# OPTIONS --allow-unsolved-metas #-}
open import Functional.State as St using (State ; F ; Cmd ; System ; trace ; save ; Memory)

module Functional.Rattle.Exec (oracle : F) where

open import Agda.Builtin.Equality
open import Data.Bool using (Bool ; if_then_else_ ; false ; true ; not)
open import Data.List using (List ; [] ; _∷_ ; map ; filter ; _++_ ; foldr ; all ; concatMap ; reverse)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Maybe.Relation.Binary.Pointwise using (dec)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∃-syntax ; Σ-syntax)
open import Function.Base using (_∘_)
open import Functional.File using (FileName ; FileContent)
open import Functional.Build using (Build ; SBuild ; SCmd ; Speculative ; Required)
open import Relation.Nullary.Decidable.Core using (isYes)
open import Relation.Nullary.Negation using (¬?)
open import Functional.Forward.Exec (oracle) using (run?)
open import Functional.Forward.Properties (oracle) using (cmdWrites ; cmdReads)
open import Functional.Rattle.Hazard (oracle) using (Hazard ; SpeculativeWriteRead ; WriteWrite ; ReadWrite ; FileInfo ; appendReads ; appendWrites ; ran)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; map₂)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_ ; _∈_)
open import Relation.Nullary using (yes ; no)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Functional.Script.Exec (oracle)  as S hiding (exec)
open import Common.List.Properties using (_before_en_)

doRun : State -> Cmd -> State
doRun (sys , mm) cmd = let sys₂ = St.run oracle cmd sys in
                           (sys₂ , save cmd ((proj₁ (trace oracle sys cmd)) ++ (proj₂ (trace oracle sys cmd))) sys₂ mm)

run : State -> Cmd -> State
run st cmd = if (run? cmd st)
             then doRun st cmd
             else st

{- do the writes of cmd intersect with files? -}
checkWritesIntersection : (x₁ : Cmd) -> (ls : List FileName) -> (s : System) -> Maybe (∃[ f₁ ](f₁ ∈ proj₂ (trace oracle s x₁) × f₁ ∈ ls))
checkWritesIntersection cmd files sys = g₁ (proj₂ (trace oracle sys cmd))
  where g₁ : (fs : List FileName) -> Maybe (∃[ f₁ ](f₁ ∈ fs × f₁ ∈ files))
        g₁ [] = nothing
        g₁ (x ∷ ws) with x ∈? files
        ... | yes x∈ = just (x , here refl , x∈)
        ... | no x∉ with g₁ ws
        ... | nothing = nothing
        ... | just (f₁ , ∈₁ , ∈₂) = just (f₁ , there ∈₁ , ∈₂)

{- did cmd write to something a cmd in the memory read? -}
checkReadWrite : {sys₀ : System} {b : Build} (x₁ : Cmd) -> (s : System) -> (ls : FileInfo sys₀ b) -> (rf : Build) -> Maybe (Hazard s x₁ ls rf)
checkReadWrite cmd sys fileInfo _ with checkWritesIntersection cmd (appendReads fileInfo) sys
... | just (f₁ , ∈₁ , ∈₂) = just (ReadWrite f₁ ∈₁ ∈₂)
... | nothing = nothing

{- did cmd write to something a cmd in the memory wrote to? -}
checkWriteWrite : {sys₀ : System} {b : Build} (x₁ : Cmd) -> (s : System) -> (ls : FileInfo sys₀ b) -> (rf : Build) -> Maybe (Hazard s x₁ ls rf)
checkWriteWrite cmd sys fileInfo _ with checkWritesIntersection cmd (appendWrites fileInfo) sys
... | just (f₁ , ∈₁ , ∈₂) = just (WriteWrite f₁ ∈₁ ∈₂)
... | nothing = nothing


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

{-
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
-}
{- -}
inter? : List FileName -> List FileName -> Maybe FileName
inter? [] ls₂ = nothing
inter? (x ∷ ls₁) ls₂ with x ∈? ls₂
... | yes x∈ls₂ = just x
... | no x∉ls₂ = inter? ls₁ ls₂

anyWriter : {sys₀ sys : System} {b : Build} (fi : FileInfo sys₀ b) (x : Cmd) (rf : Build) -> Maybe (∃[ x₁ ](∃[ f₁ ](∃[ xs ](∃[ ys ](xs ++ x₁ ∷ ys ≡ (ran fi) × f₁ ∈ cmdWrites x₁ (S.exec sys₀ xs) × f₁ ∈ cmdReads x sys × x before x₁ en rf)))))
anyWriter FileInfo.[] x rf = nothing
anyWriter {sys₀} {sys} {b} (FileInfo.Skip x₁ fi) x rf = anyWriter fi x rf
anyWriter {sys₀} {sys} (FileInfo.Run x₁ fi) x rf = {!!}

{- with inter? ws (cmdReads x sys)
-- need evidence the file is in the writes of x₁ and in the reads of x; so how do i do that
-- 
  where inter? : List FileName -> List FileName -> Maybe FileName
        inter? [] ls₂ = nothing
        inter? (x ∷ ls₁) ls₂ with x ∈? ls₂
        ... | yes _ = {!!}
        ... | no _ = {!!}
... | nothing = {!!}
... | just f₁ = {!!}
-}

{- make sure all cmd's which wrote to a file this cmd read, have been required,
if cmd has been required -}
{- 1. check if cmd has been required; if not then return false
   2. find a list of cmds that write to a file cmd reads
   3. check that each of them is before cmd in the reference list. 
-}
checkWriteRead : {sys₀ : System} {b : Build} (s : State) -> (ls : FileInfo sys₀ b) -> (x₁ : Cmd) -> (rf : Build) -> Maybe (Hazard (proj₁ s) x₁ ls rf)
checkWriteRead (sys , mm) fi cmd rf with cmd ∈? rf
... | no cmd∉ = nothing
... | yes cmd∈ = if required? cmd mm rf cmd∈
                 then {!!}
                 {-
                 then (let writers = getWriters (proj₁ (trace oracle sys cmd)) fi in -- get all of the cmds in memory that write to a file this cmd read
                          if all (isAfter? rf cmd cmd∈) writers
                          then nothing
                          else just (SpeculativeWriteRead {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!})) -}
                 else nothing

hasHazard : {sys₀ : System} {b : Build} (s : State) -> (ls : FileInfo sys₀ b) -> (x₁ : Cmd) -> (rf : Build) -> Maybe (Hazard (proj₁ s) x₁ ls rf)
hasHazard st@(sys , mm) fi cmd rf with checkWriteRead st fi cmd rf
... | just hz = just hz
... | nothing with checkWriteWrite cmd sys fi rf 
... | just hz = just hz
... | nothing = checkReadWrite cmd sys fi rf


doRunCheck : {sys₀ : System} {b : Build} (s : State) -> (ls : FileInfo sys₀ b) -> (x₁ : Cmd) -> (rf : Build) -> (Hazard (proj₁ s) x₁ ls rf) ⊎ (State × FileInfo sys₀ (b ++ x₁ ∷ []))
doRunCheck st@(sys , mm) fi cmd rf with hasHazard st fi cmd rf
... | just hz = inj₁ hz
... | nothing = inj₂ ((doRun st cmd) , FileInfo.Run cmd fi)
--(cmd , proj₁ (trace oracle sys cmd) , proj₂ (trace oracle sys cmd)) ∷ fi)
    

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

runWError : {sys₀ : System} {b : Build} (s : State) -> (ls : FileInfo sys₀ b) -> (x₁ : Cmd) -> (rf : Build) -> (Hazard (proj₁ s) x₁ ls rf) ⊎ (State × FileInfo sys₀ (b ++ x₁ ∷ []))
runWError st@(sys , mm) fi cmd rf with run? cmd st
... | true with doRunCheck st fi cmd rf
... | inj₁ hz = inj₁ hz
... | inj₂ (a , snd) = inj₂ (a , snd)
runWError st@(sys , mm) fi cmd rf | false = inj₂ (st , FileInfo.Skip cmd fi)

exec : State -> Build -> State
exec st [] = st
exec st (x ∷ b) = exec (run st x) b

{- -}
execWError : {sys₀ : System} {b : Build} -> (State × FileInfo sys₀ b) -> Build -> (rf : Build) -> ∃[ s ](∃[ x₁ ](∃[ b₁ ](Σ[ ls ∈ FileInfo sys₀ b₁ ](Hazard s x₁ ls rf)))) ⊎ ∃[ b₁ ](State × FileInfo sys₀ b₁)
execWError {sys₀} {b} stfi [] _ = inj₂ (b , stfi)
execWError {sys₀} {b₁} (st , fi) (x ∷ b) rf with runWError {sys₀} {b₁} st fi x rf
... | inj₁ hz = inj₁ (proj₁ st , (x , (b₁ , fi , hz)))
... | inj₂ stfi = execWError {sys₀} {b₁ ++ x ∷ []} stfi b rf
{-
... | inj₁ (fst , fst₁ , fst₂ , snd) = inj₁ (fst , (fst₁ , (fst₂ , snd)))
... | inj₂ y = inj₂ {!!}
-}

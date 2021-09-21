\begin{code}[hide]
open import Functional.State using (Oracle ; Cmd ; FileSystem)

module Functional.Script.Hazard.Base (oracle : Oracle) where

open import Agda.Builtin.Equality
open import Functional.State.Helpers (oracle) using (cmdWriteNames ; cmdReadNames ; run)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Nat.Properties as N using (1+n≢n ; ≤-refl ; ≤-step)
open import Data.Bool using (true ; false)
open import Data.Nat using (_>_)
open import Data.List using (List ; [] ; _∷_ ; _∷ʳ_  ; _++_ ; map ; foldl ; filter ; concatMap ; length ; concat)
open import Data.List.Properties using (concat-++ ; map-++-commute ; ∷-injectiveˡ ; ∷-injectiveʳ)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_ ; Σ-syntax ; ∃-syntax) 
open import Data.Product.Properties using (,-injectiveˡ ; ,-injectiveʳ)
open import Functional.File using (FileName)
open import Functional.Build (oracle) using (Build)
open import Data.List.Membership.Propositional using (_∈_ ; _∉_)

open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Relation.Nullary using (yes ; no ; ¬_ ; Dec)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Common.List.Properties using (_before_∈_)
open import Function using (_∘_)
open import Data.String.Properties using (_≟_ ; ≡-decSetoid)
open import Data.List.Membership.DecSetoid (≡-decSetoid) using (_∈?_) 
open import Data.List.Relation.Unary.Any using (tail)
open import Data.List.Relation.Unary.All using (All ; lookup ; _∷_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (concat⁺ ; map⁺ ; filter-⊆ ; filter⁺′ ; ++⁺)
open import Data.List.Relation.Unary.Any using (there ; here)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-decidable ; ≡×≡⇒≡)
open import Data.List.Relation.Binary.Equality.DecPropositional (_≟_) using (_≡?_)
open import Relation.Binary.PropositionalEquality using (subst ; subst₂ ; cong ; sym ; trans)
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.AllPairs using (AllPairs ; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)


{- Hazards:

Do not depend on a reference order:

   Read before Write
   Write before Write

Does depend on a reference order:
  
  Speculative Write before Read


---------------------------------------

Goals (what we need):

execWError says there is either a hazard or a state

completeness takes evidence that the build has no hazards and proves that execWerror will return 
a state and not a hazard.  fundamentally this works by producing a contradiction when execWError
returns a hazard with the hazardfree evidence. 

What would be ideal is if hazard and hazardfree are set up in such a way that we can just say
contradiction 'hazard free evidnece' 'hazard evidence' without anymore manipulation

Existing hazardfree defs:

HazardFree is recursive and says the writes of the command at the head of the list are disjoint from the writes/reads that happened previously (exist in some list)

Would be nice to stick with this so i dont have to completely redo a lot of my proofs.  

HazardFreeReordering says 2 builds are permutations of one another. which could jsut be passed as its own argument to a function

Says both of the builds are hazardFree (by above def). 
And says there is not speculativewrhazard in the first of the 2 builds.  

speculativewrhazard says there are two commands, such that the first command is first in the original build, and the 2nd command writes to something before the first command in the build that is running.

this definition is just so long and ugly.  

-}
FileNames : Set
FileNames = List FileName
\end{code}

\newcommand{\fileinfo}{%
\begin{code}
-- the files a command read and wrote
FileInfo : Set
FileInfo = List (Cmd × FileNames × FileNames)
\end{code}}

\begin{code}[hide]
save : FileSystem → Cmd → FileInfo → FileInfo
save s x fi = (x , (cmdReadNames x s) , (cmdWriteNames x s)) ∷ fi

cmdsRun : FileInfo → List Cmd
cmdsRun = map proj₁

filesRead : FileInfo → List FileName
filesRead = concatMap (proj₁ ∘ proj₂)

∈-concatMap-++ : ∀ {v : FileName} f (xs : FileInfo) ys zs → v ∈ concatMap f (xs ++ zs) → v ∈ concatMap f (xs ++ ys ++ zs)
∈-concatMap-++ f xs ys zs v∈ with ∈-++⁻ (concat (map f xs)) (subst (λ x → _ ∈ x) ≡₁ v∈)
  where ≡₁ : concatMap f (xs ++ zs) ≡ concat (map f xs) ++ concat (map f zs)
        ≡₁ = trans (cong concat (map-++-commute f xs zs)) (sym (concat-++ (map f xs) (map f zs)))
... | inj₁ v∈xs = subst (λ x → _ ∈ x) ≡₁ (∈-++⁺ˡ v∈xs)
  where ≡₁ : concat (map f xs) ++ concat (map f (ys ++ zs)) ≡ concat (map f (xs ++ ys ++ zs))
        ≡₁ = trans (concat-++ (map f xs) (map f (ys ++ zs))) (cong concat (sym (map-++-commute f xs (ys ++ zs))))
... | inj₂ v∈ys = subst (λ x → _ ∈ x) ≡₁ (∈-++⁺ʳ (concat (map f xs)) (∈-++⁺ʳ (concat (map f ys)) v∈ys))
  where ≡₁ : concat (map f xs) ++ concat (map f ys) ++ concat (map f zs) ≡ concat (map f (xs ++ ys ++ zs))
        ≡₁ = trans (cong (concat (map f xs) ++_) (concat-++ (map f ys) (map f zs)))
                   (trans (concat-++ (map f xs) (map f ys ++ map f zs))
                          (cong concat (trans (cong (map f xs ++_) (sym (map-++-commute f ys zs)))
                                       (sym (map-++-commute f xs (ys ++ zs))))))


∈-filesRead-++ : ∀ {v} xs ys zs → v ∈ filesRead (xs ++ zs) → v ∈ filesRead (xs ++ ys ++ zs)
∈-filesRead-++ = ∈-concatMap-++ (proj₁ ∘ proj₂)

filesWrote : FileInfo → List FileName
filesWrote = concatMap (proj₂ ∘ proj₂)

∈-filesWrote-++ : ∀ {v} xs ys zs → v ∈ filesWrote (xs ++ zs) → v ∈ filesWrote (xs ++ ys ++ zs)
∈-filesWrote-++ = ∈-concatMap-++ (proj₂ ∘ proj₂)

files : FileInfo → List FileName
files ls = (filesRead ls) ++ (filesWrote ls)

∈-files-++ : ∀ {v} xs ys zs → v ∈ files (xs ++ zs) → v ∈ files (xs ++ ys ++ zs)
∈-files-++ xs ys zs v∈files with ∈-++⁻ (filesRead (xs ++ zs)) v∈files
... | inj₁ v∈reads = ∈-++⁺ˡ (∈-filesRead-++ xs ys zs v∈reads)
... | inj₂ v∈writes = ∈-++⁺ʳ (filesRead (xs ++ ys ++ zs)) (∈-filesWrote-++ xs ys zs v∈writes)

cmdWrote : FileInfo → Cmd → List FileName
cmdWrote [] p = []
cmdWrote (x ∷ ls) p with (proj₁ x) ≟ p
... | yes x≡p = proj₂ (proj₂ x)
... | no ¬x≡p = cmdWrote ls p


cmdWrote∷-≡ : ∀ x ls → cmdWrote (x ∷ ls) (proj₁ x) ≡ proj₂ (proj₂ x)
cmdWrote∷-≡ x ls with (proj₁ x) ≟ (proj₁ x)
... | yes x≡x = refl
... | no ¬x≡x = contradiction refl ¬x≡x

∈-cmdWrote∷l : ∀ {v} x ls → v ∈ proj₂ (proj₂ x) → v ∈ cmdWrote (x ∷ ls) (proj₁ x)
∈-cmdWrote∷l x ls v∈ with (proj₁ x) ≟ (proj₁ x)
... | no ¬x≡x = contradiction refl ¬x≡x
... | yes x≡x = v∈

∈-cmdWrote∷ : ∀ {v} x x₁ ls → v ∈ cmdWrote ls x₁ → ¬ (proj₁ x) ≡ x₁ → v ∈ cmdWrote (x ∷ ls) x₁
∈-cmdWrote∷ x x₁ ls v∈ ¬≡ with (proj₁ x) ≟ x₁
... | yes x≡x₁ = contradiction x≡x₁ ¬≡
... | no ¬x≡x₁ = v∈

-- if there is a file in the cmdRead for x , then x ∈ xs
lemma2 : ∀ {v} x xs → v ∈ cmdWrote xs x → x ∈ map proj₁ xs
lemma2 x (x₁ ∷ xs) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = here (sym x₁≡x)
... | no ¬x₁≡x = there (lemma2 x xs v∈)

∈-cmdWrote++⁺ʳ : ∀ {v} x xs ys → Unique (map proj₁ (xs ++ ys)) → v ∈ cmdWrote ys x → v ∈ cmdWrote (xs ++ ys) x
∈-cmdWrote++⁺ʳ x [] ys u v∈ = v∈
∈-cmdWrote++⁺ʳ x (x₁ ∷ xs) ys (px₁ ∷ u) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = contradiction x₁≡x (lookup px₁ x∈xs++ys)
  where x∈xs++ys : x ∈ map proj₁ (xs ++ ys)
        x∈xs++ys = subst (λ ls → _ ∈ ls) (sym (map-++-commute proj₁ xs ys)) (∈-++⁺ʳ (map proj₁ xs) (lemma2 x ys v∈))
... | no ¬x₁≡x = ∈-cmdWrote++⁺ʳ x xs ys u v∈

∈-cmdWrote++mid : ∀ {v} x xs ys zs → Unique (map proj₁ (xs ++ ys ++ zs)) → v ∈ cmdWrote (xs ++ zs) x → v ∈ cmdWrote (xs ++ ys ++ zs) x
∈-cmdWrote++mid x [] ys zs u v∈ = ∈-cmdWrote++⁺ʳ x ys zs u v∈
∈-cmdWrote++mid x (x₁ ∷ xs) ys zs (px₁ ∷ u) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = v∈
... | no ¬x₁≡x = ∈-cmdWrote++mid x xs ys zs u v∈



cmdRead : FileInfo → Cmd → List FileName
cmdRead [] p = []
cmdRead (x ∷ ls) p with (proj₁ x) ≟ p
... | yes x≡p = proj₁ (proj₂ x)
... | no ¬x≡p = cmdRead ls p

∈-cmdRead∷l : ∀ {v} x ls → v ∈ proj₁ (proj₂ x) → v ∈ cmdRead (x ∷ ls) (proj₁ x)
∈-cmdRead∷l x ls v∈ with (proj₁ x) ≟ (proj₁ x)
... | no ¬x≡x = contradiction refl ¬x≡x
... | yes x≡x = v∈

∈-cmdRead∷ : ∀ {v} x x₁ ls → v ∈ cmdRead ls x₁ → ¬ (proj₁ x) ≡ x₁ → v ∈ cmdRead (x ∷ ls) x₁
∈-cmdRead∷ x x₁ ls v∈ ¬≡ with (proj₁ x) ≟ x₁
... | yes x≡x₁ = contradiction x≡x₁ ¬≡
... | no ¬x≡x₁ = v∈

-- if there is a file in the cmdRead for x , then x ∈ xs
lemma1 : ∀ {v} x xs → v ∈ cmdRead xs x → x ∈ map proj₁ xs
lemma1 x (x₁ ∷ xs) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = here (sym x₁≡x)
... | no ¬x₁≡x = there (lemma1 x xs v∈)

∈-cmdRead++⁺ʳ : ∀ {v} x xs ys → Unique (map proj₁ (xs ++ ys)) → v ∈ cmdRead ys x → v ∈ cmdRead (xs ++ ys) x
∈-cmdRead++⁺ʳ x [] ys u v∈ = v∈
∈-cmdRead++⁺ʳ x (x₁ ∷ xs) ys (px₁ ∷ u) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = contradiction x₁≡x (lookup px₁ x∈xs++ys)
  where x∈xs++ys : x ∈ map proj₁ (xs ++ ys)
        x∈xs++ys = subst (λ ls → _ ∈ ls) (sym (map-++-commute proj₁ xs ys)) (∈-++⁺ʳ (map proj₁ xs) (lemma1 x ys v∈))
... | no ¬x₁≡x = ∈-cmdRead++⁺ʳ x xs ys u v∈

∈-cmdRead++mid : ∀ {v} x xs ys zs → Unique (map proj₁ (xs ++ ys ++ zs)) → v ∈ cmdRead (xs ++ zs) x → v ∈ cmdRead (xs ++ ys ++ zs) x
∈-cmdRead++mid x [] ys zs u v∈ = ∈-cmdRead++⁺ʳ x ys zs u v∈
∈-cmdRead++mid x (x₁ ∷ xs) ys zs (px₁ ∷ u) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = v∈
... | no ¬x₁≡x = ∈-cmdRead++mid x xs ys zs u v∈

--  ¬speculativehazard def only makes sense with unique FileINfo and build
\end{code}

\newcommand{\speculative}{%
\begin{code}
¬SpeculativeHazard : Build → FileInfo → Set
¬SpeculativeHazard b ls = ∀ x₁ x₂ → x₂ before x₁ ∈ (cmdsRun ls) → x₂ ∈ b → ¬ x₁ before x₂ ∈ b → Disjoint (cmdRead ls x₂) (cmdWrote ls x₁)
\end{code}}

\begin{code}[hide]
{- we have a Speculative hazard if a required command read something a speculative command wrote to. 
 So we need to be able to determine: 
1. when a command is required : a command is required if its the first command in the list?

2. when a command is speculated
-}
-- (cmdsRun (save x (cmdReadNames x s) (cmdWriteNames x s) ls))
-- (save x (cmdReadNames x s) (cmdWriteNames x s) ls)
-- (save x (cmdReadNames x s) (cmdWriteNames x s) ls)


\end{code}

\newcommand{\hazard}{%
\begin{code}
data Hazard : FileSystem → Cmd → Build → FileInfo → Set where
  ReadWrite   : ∀ s x {b} ls v → v ∈ (cmdWriteNames x s) → v ∈ (filesRead ls) → Hazard s x b ls
  WriteWrite  : ∀ s x {b} ls v → v ∈ (cmdWriteNames x s) → v ∈ (filesWrote ls) → Hazard s x b ls
  Speculative : ∀ s x b ls x₁ x₂ v → x₂ before x₁ ∈ (x ∷ (cmdsRun ls)) → x₂ ∈ b → ¬ x₁ before x₂ ∈ b
                → v ∈ cmdRead (save s x ls) x₂ → v ∈ cmdWrote (save s x ls) x₁ → Hazard s x b ls
\end{code}}

\begin{code}[hide]
∃Hazard : Build → Set
∃Hazard b = ∃[ sys ](∃[ x ](∃[ ls ](Hazard sys x b ls)))
\end{code}

\newcommand{\hfcmd}{%
\begin{code}
data HazardFreeCmd : FileSystem → Cmd → Build → FileInfo → Set where
  HFC : ∀ {s} {ls} {x} {b₂} → ¬SpeculativeHazard b₂ (save s x ls) → Disjoint (cmdWriteNames x s) (files ls) → HazardFreeCmd s x b₂ ls
\end{code}}
\begin{code}[hide]
hazardContradiction : ∀ s x b₂ ls → (hz : Hazard s x b₂ ls) → HazardFreeCmd s x b₂ ls → ⊥
hazardContradiction s x b ls hz (HFC ¬sh dsj) with hz
... | ReadWrite .s .x .ls v v∈cw v∈rs = contradiction (v∈cw , ∈-++⁺ˡ v∈rs) dsj
... | WriteWrite .s .x .ls v v∈cw v∈ws = contradiction (v∈cw , ∈-++⁺ʳ (filesRead ls) v∈ws) dsj
... | Speculative .s .x .b .ls x₁ x₂ v bf x₂∈b ¬bf v∈rs v∈ws = contradiction (v∈rs , v∈ws) (¬sh x₁ x₂ bf x₂∈b ¬bf)
\end{code}

\newcommand{\hazardfree}{%
\begin{code}
data HazardFree : FileSystem → Build → Build → FileInfo → Set where
  [] : ∀ {s} {b} {ls} → HazardFree s [] b ls
  :: : ∀ s ls x b₁ b₂ → ¬ Hazard s x b₂ ls → HazardFree (run x s) b₁ b₂ (save s x ls) → HazardFree s (x ∷ b₁) b₂ ls
\end{code}}


\begin{code}[hide]

intersection?2 : (xs ys : FileNames) → Dec (∃[ v ](v ∈ xs × v ∈ ys))
intersection?2 [] ys = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ (∃[ v ](v ∈ [] × v ∈ ys))
        g₁ ()
intersection?2 (x ∷ xs) ys with x ∈? ys
... | yes x∈ys = true Relation.Nullary.because Relation.Nullary.ofʸ g₁
  where g₁ : ∃[ v ](v ∈ x ∷ xs × v ∈ ys)
        g₁ = x , here refl , x∈ys
... | no x∉ys with intersection?2 xs ys
... | yes (v , v∈xs , v∈ys) = true Relation.Nullary.because Relation.Nullary.ofʸ (v , there v∈xs , v∈ys)
... | no ¬p = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ (∃[ v ](v ∈ x ∷ xs × v ∈ ys))
        g₁ (v , v∈x∷xs , v∈ys) with v ≟ x
        ... | yes v≡x = contradiction (subst (λ x₁ → x₁ ∈ ys) v≡x v∈ys) x∉ys
        ... | no ¬v≡x = ¬p (v , (tail ¬v≡x v∈x∷xs) , v∈ys)

intersection? : (xs ys : FileNames) → Dec (Disjoint xs ys)
intersection? [] ys = true Relation.Nullary.because Relation.Nullary.ofʸ (λ ())
intersection? (x ∷ xs) ys with x ∈? ys
... | yes x∈ys = false Relation.Nullary.because Relation.Nullary.ofⁿ λ x₁ → x₁ ((here refl) , x∈ys)
... | no x∉ys with intersection? xs ys
... | yes dsj = true Relation.Nullary.because Relation.Nullary.ofʸ λ x₁ → g₁ x₁
  where g₁ : ∀ {v} → (v ∈ x ∷ xs × v ∈ ys) → ⊥
        g₁ {v} (v∈x∷xs , v∈ys) with v ≟ x
        ... | yes v≡x = x∉ys (subst (λ x₁ → x₁ ∈ ys) v≡x v∈ys)
        ... | no ¬v≡x = dsj (tail ¬v≡x v∈x∷xs , v∈ys)
... | no ¬dsj = false Relation.Nullary.because Relation.Nullary.ofⁿ λ x₁ → ¬dsj λ x₂ → x₁ (there (proj₁ x₂) , proj₂ x₂)

before? : ∀ (x₁ : Cmd) x b → Dec (x₁ before x ∈ b)
before? x₁ x [] = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ (x₁ before x ∈ [])
        g₁ (xs , ys , ≡₁ , x∈ys) = contradiction (subst (λ x₂ → x ∈ x₂) (sym ≡₁) (∈-++⁺ʳ xs (there x∈ys))) λ ()
before? x₁ x (x₂ ∷ b) with x₁ ≟ x₂
... | yes x₁≡x₂ with x ∈? b
... | yes x∈b = true Relation.Nullary.because Relation.Nullary.ofʸ g₁
  where g₁ : x₁ before x ∈ (x₂ ∷ b)
        g₁ = [] , b , cong (_∷ b) (sym x₁≡x₂) , x∈b
... | no x∉b = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ (x₁ before x ∈ (x₂ ∷ b))
        g₁ ([] , ys , x₂∷b≡x₁∷ys , x∈ys) = contradiction (subst (λ x₃ → x ∈ x₃) (sym (∷-injectiveʳ x₂∷b≡x₁∷ys)) x∈ys) x∉b
        g₁ (x₃ ∷ xs , ys , x₂∷b≡xs++x₁∷ys , x∈ys) = contradiction (subst (λ x₄ → x ∈ x₄) (sym (∷-injectiveʳ x₂∷b≡xs++x₁∷ys)) (∈-++⁺ʳ xs (there x∈ys))) x∉b
before? x₁ x (x₂ ∷ b) | no ¬x₁≡x₂ with before? x₁ x b
... | yes (xs , ys , ≡₁ , x∈ys)
  = true Relation.Nullary.because Relation.Nullary.ofʸ (x₂ ∷ xs , ys , cong (x₂ ∷_) ≡₁ , x∈ys)
... | no ¬bf = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ (x₁ before x ∈ (x₂ ∷ b))
        g₁ ([] , ys , ≡₁ , x∈ys) = contradiction (sym (∷-injectiveˡ ≡₁)) ¬x₁≡x₂
        g₁ (x₃ ∷ xs , ys , ≡₁ , x∈ys) = ¬bf (xs , ys , ∷-injectiveʳ ≡₁ , x∈ys)

{- does there exist a command in ls that writes to these files and is not before x in b? -}

speculativeHazard-x? : ∀ x b₂ ls ls₁ rs → Dec (∃[ x₁ ](∃[ v ](x₁ ∈ ls × ¬ (x₁ before x ∈ b₂) × v ∈ rs × v ∈ cmdWrote ls₁ x₁)))
speculativeHazard-x? x b₂ [] ls₁ rs = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ∃[ x₁ ](∃[ v ](x₁ ∈ [] × ¬ (x₁ before x ∈ b₂) × v ∈ rs × v ∈ cmdWrote ls₁ x₁)) → ⊥
        g₁ ()
speculativeHazard-x? x b₂ (x₁ ∷ ls) ls₁ rs with intersection?2 rs (cmdWrote ls₁ x₁)
... | yes (v , v∈rs , v∈ws) with before? x₁ x b₂
... | no ¬bf = true Relation.Nullary.because Relation.Nullary.ofʸ g₁
  where g₁ : ∃[ x₂ ](∃[ v ](x₂ ∈ (x₁ ∷ ls) × ¬ (x₂ before x ∈ b₂) × v ∈ rs × v ∈ cmdWrote ls₁ x₂))
        g₁ = x₁ , v , here refl , ¬bf , v∈rs , v∈ws
... | yes bf with speculativeHazard-x? x b₂ ls ls₁ rs
... | yes (x₂ , v₂ , x₂∈ , ¬bf , a , a₁) = true Relation.Nullary.because Relation.Nullary.ofʸ g₁
  where g₁ : ∃[ x₂ ](∃[ v ](x₂ ∈ (x₁ ∷ ls) × ¬ (x₂ before x ∈ b₂) × v ∈ rs × v ∈ cmdWrote ls₁ x₂))
        g₁ = x₂ , v₂ , there x₂∈ , ¬bf , a , a₁
... | no ¬p = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ (∃[ x₂ ](∃[ v ](x₂ ∈ (x₁ ∷ ls) × ¬ (x₂ before x ∈ b₂) × v ∈ rs × v ∈ cmdWrote ls₁ x₂)))
        g₁ (x₂ , v , x₂∈ , ¬bf , v∈rs , v∈ws) with x₂ ≟ x₁
        ... | yes x₂≡x₁ = contradiction (subst (λ x₃ → x₃ before x ∈ b₂) (sym x₂≡x₁) bf) ¬bf
        ... | no ¬x₂≡x₁ = ¬p (x₂ , v , tail ¬x₂≡x₁ x₂∈ , ¬bf , v∈rs , v∈ws)
speculativeHazard-x? x b₂ (x₁ ∷ ls) ls₁ rs | no p₁ with speculativeHazard-x? x b₂ ls ls₁ rs
... | yes (x₂ , v₂ , x₂∈ , ¬bf , a , a₁) = true Relation.Nullary.because Relation.Nullary.ofʸ g₁
  where g₁ : ∃[ x₂ ](∃[ v ](x₂ ∈ (x₁ ∷ ls) × ¬ (x₂ before x ∈ b₂) × v ∈ rs × v ∈ cmdWrote ls₁ x₂))
        g₁ = x₂ , v₂ , there x₂∈ , ¬bf , a , a₁
... | no ¬p = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ (∃[ x₂ ](∃[ v ](x₂ ∈ (x₁ ∷ ls) × ¬ (x₂ before x ∈ b₂) × v ∈ rs × v ∈ cmdWrote ls₁ x₂)))
        g₁ (x₂ , v , x₂∈ , ¬bf , v∈rs , v∈ws) with x₂ ≟ x₁
        ... | yes x₂≡x₁ = p₁ (v , (v∈rs , subst (λ x₃ → v ∈ cmdWrote ls₁ x₃) x₂≡x₁ v∈ws))
        ... | no ¬x₂≡x₁ = ¬p (x₂ , v , tail ¬x₂≡x₁ x₂∈ , ¬bf , v∈rs , v∈ws)

¬speculative? : ∀ b₂ ls → Dec (∃[ x₁ ](∃[ x₂ ](∃[ v ]((x₂ before x₁ ∈ (map proj₁ ls)) × x₂ ∈ b₂ × ¬ (x₁ before x₂ ∈ b₂) × v ∈ cmdRead ls x₂ × v ∈ cmdWrote ls x₁))))
¬speculative? b₂ ls = g₁ b₂ (map proj₁ ls) ls
  where g₁ : ∀ b₂ ls₁ ls₂ → Dec (∃[ x₁ ](∃[ x₂ ](∃[ v ]((x₂ before x₁ ∈ ls₁) × x₂ ∈ b₂ × ¬ (x₁ before x₂ ∈ b₂) × v ∈ cmdRead ls₂ x₂ × v ∈ cmdWrote ls₂ x₁))))
        g₁ b₂ [] ls₂ = false Relation.Nullary.because Relation.Nullary.ofⁿ g₂
          where g₂ : ¬ (∃[ x₁ ](∃[ x₂ ](∃[ v ]((x₂ before x₁ ∈ []) × x₂ ∈ b₂ × ¬ (x₁ before x₂ ∈ b₂) × v ∈ cmdRead ls₂ x₂ × v ∈ cmdWrote ls₂ x₁))))
                g₂ (_ , _ , _ , (xs , ys , ≡₁ , x₁∈ys) , rest)
                  = contradiction (subst (λ x → _ ∈ x) (sym ≡₁) (∈-++⁺ʳ xs (there x₁∈ys))) (λ ())
        g₁ b₂ (x ∷ ls₁) ls₂ with x ∈? b₂
        ... | yes x∈b₂ with speculativeHazard-x? x b₂ ls₁ ls₂ (cmdRead ls₂ x)
        ... | yes (x₁ , v , x₁∈ls , ¬bf , v∈rs , v∈ws)
          = true Relation.Nullary.because Relation.Nullary.ofʸ (x₁ , x , v , ([] , ls₁ , refl , x₁∈ls) , x∈b₂ , ¬bf , v∈rs , v∈ws)
        ... | no ¬p with g₁ b₂ ls₁ ls₂
        ... | yes (x₁ , x₂ , v , (xs , ys , ≡₁ , ∈₁) , rest)
          = true Relation.Nullary.because Relation.Nullary.ofʸ (x₁ , x₂ , v , (x ∷ xs , ys , cong (x ∷_) ≡₁ , ∈₁) , rest)
        ... | no ¬sh = false Relation.Nullary.because Relation.Nullary.ofⁿ g₂
          where g₂ : ¬ (∃[ x₁ ](∃[ x₂ ](∃[ v ]((x₂ before x₁ ∈ (x ∷ ls₁)) × x₂ ∈ b₂ × ¬ (x₁ before x₂ ∈ b₂) × v ∈ cmdRead ls₂ x₂ × v ∈ cmdWrote ls₂ x₁))))
                g₂ (x₁ , x₂ , v , ([] , ys , ≡₁ , ∈₁) , x₂∈b₂ , ¬bf , v∈rs , v∈ws)
                  = ¬p (x₁ , v , subst (λ x₃ → x₁ ∈ x₃) (sym (∷-injectiveʳ ≡₁)) ∈₁ , subst (λ x₃ → ¬ (x₁ before x₃ ∈ b₂)) (sym (∷-injectiveˡ ≡₁)) ¬bf
                       , subst (λ x₃ → v ∈ cmdRead ls₂ x₃) (sym (∷-injectiveˡ ≡₁)) v∈rs , v∈ws)
                g₂ (x₁ , x₂ , v , (x₃ ∷ xs , ys , ≡₁ , ∈₁) , rest) = ¬sh (x₁ , x₂ , v , (xs , ys , (∷-injectiveʳ ≡₁) , ∈₁) , rest)
        g₁ b₂ (x ∷ ls₁) ls₂ | no x∉b₂ with g₁ b₂ ls₁ ls₂
        ... | yes (x₁ , x₂ , v , (xs , ys , ≡₁ , ∈₁) , rest)
          = true Relation.Nullary.because Relation.Nullary.ofʸ (x₁ , x₂ , v , (x ∷ xs , ys , cong (x ∷_) ≡₁ , ∈₁) , rest)
        ... | no ¬sh = false Relation.Nullary.because Relation.Nullary.ofⁿ g₂
          where g₂ : ¬ (∃[ x₁ ](∃[ x₂ ](∃[ v ]((x₂ before x₁ ∈ (x ∷ ls₁)) × x₂ ∈ b₂ × ¬ (x₁ before x₂ ∈ b₂) × v ∈ cmdRead ls₂ x₂ × v ∈ cmdWrote ls₂ x₁))))
                g₂ (x₁ , x₂ , v , ([] , ys , ≡₁ , ∈₁) , x₂∈b₂ , ¬bf , v∈rs , v∈ws)
                  = contradiction (subst (λ x₃ → x₃ ∈ b₂) (sym (∷-injectiveˡ ≡₁)) x₂∈b₂) x∉b₂
                g₂ (x₁ , x₂ , v , (x₃ ∷ xs , ys , ≡₁ , ∈₁) , rest) = ¬sh (x₁ , x₂ , v , (xs , ys , (∷-injectiveʳ ≡₁) , ∈₁) , rest)

hazard? : ∀ s x b₂ ls → Dec (Hazard s x b₂ ls)
hazard? s x b₂ ls with intersection?2 (cmdWriteNames x s) (filesRead ls)
... | yes (v , ∈₁ , ∈₂) = true Relation.Nullary.because Relation.Nullary.ofʸ (ReadWrite s x {b₂} ls v ∈₁ ∈₂)
... | no ¬x₁ with intersection?2 (cmdWriteNames x s) (filesWrote ls)
... | yes (v , ∈₁ , ∈₂) = true Relation.Nullary.because Relation.Nullary.ofʸ (WriteWrite s x {b₂} ls v ∈₁ ∈₂)
... | no ¬x₂ with ¬speculative? b₂ (save s x ls)
... | yes (x₁ , x₂ , v , bf , x₂∈b₂ , ¬bf , v∈₁ , v∈₂)
  = true Relation.Nullary.because Relation.Nullary.ofʸ (Speculative s x b₂ ls x₁ x₂ v bf x₂∈b₂ ¬bf v∈₁ v∈₂)
... | no ¬sh = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ Hazard s x b₂ ls
        g₁ (ReadWrite .s _ .ls v x x₁) = ¬x₁ (v , (x , x₁))
        g₁ (WriteWrite .s _ .ls v x x₁) = ¬x₂ (v , (x , x₁))
        g₁ (Speculative .s _ .b₂ .ls x₁ x₂ v y x₃ x₄ x₅ x₆)
          = ¬sh (x₁ , x₂ , v , y , x₃ , x₄ , x₅ , x₆)

hazardfree? : ∀ s b₁ b₂ ls → Dec (HazardFree s b₁ b₂ ls)
hazardfree? s [] b₂ ls = true Relation.Nullary.because Relation.Nullary.ofʸ []
hazardfree? s (x ∷ b₁) b₂ ls with hazard? s x b₂ ls
... | yes hz = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ HazardFree s (x ∷ b₁) b₂ ls
        g₁ (:: .s .ls _ .b₁ .b₂ ¬hz hf) = ¬hz hz
... | no ¬hz with hazardfree? (run x s) b₁ b₂ (save s x ls)
... | yes hf = true Relation.Nullary.because Relation.Nullary.ofʸ (:: s ls x b₁ b₂ ¬hz hf)
... | no ¬hf = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ HazardFree s (x ∷ b₁) b₂ ls
        g₁ (:: .s .ls _ .b₁ .b₂ x hf) = ¬hf hf
\end{code}

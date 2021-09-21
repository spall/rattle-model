\begin{code}[hide]
open import Functional.State as St using (Oracle ; FileSystem ; Cmd)

module Functional.Script.Exec (oracle : Oracle) where

open import Common.List.Properties as CLP using (_before_en_ ; before-∷ʳ⁺)
open import Functional.State.Helpers (oracle) using (run ; cmdReadNames ; cmdWriteNames ; cmdReadWriteNames)
open import Functional.State.Properties (oracle) using (lemma1-sym ; lemma5 ; run-≡)
open import Agda.Builtin.Equality
open import Data.Sum using (_⊎_)
open import Data.List using ([] ; _∷_ ; List ; map ; _++_ ; _∷ʳ_ ; [_] ; foldr ; reverse)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∄-syntax ; ∃-syntax ; Σ-syntax)

open import Functional.Build (oracle) using (Build)
open import Functional.File using (FileName ; Files)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Relation.Binary.PropositionalEquality using (decSetoid ; trans ; sym ; subst ; cong ; cong₂) 
open import Data.String.Properties using (_≟_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Data.List.Properties using (∷-injective ; ∷-injectiveʳ ; ∷-injectiveˡ ; ++-identityʳ)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-insert ; ∈-∃++ ; ∈-resp-≋)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ ; ++⁻ʳ ; ++⁻ )
open import Function using (_∘_)
\end{code}

\newcommand{\script}{%
\begin{code}
script : FileSystem -> Build -> FileSystem
script sys [] = sys
script sys (x ∷ b) = script (run x sys) b
\end{code}}

\begin{code}[hide]
buildReadNames : FileSystem -> Build -> List FileName
buildReadNames _ [] = []
buildReadNames sys (x ∷ b) = (cmdReadNames x sys) ++ buildReadNames (run x sys) b

buildWriteNames : FileSystem -> Build -> List FileName
buildWriteNames _ [] = []
buildWriteNames sys (x ∷ b) = (cmdWriteNames x sys) ++ buildWriteNames (run x sys) b

build-rws : FileSystem -> Build -> List FileName -> List FileName
build-rws sys [] ls = ls
build-rws sys (x ∷ b) ls = build-rws (run x sys) b (cmdReadWriteNames x sys ++ ls)


-- proofs to go in own file eventually:        

-- use this instead of h₂
h₄ : (s s₁ : FileSystem) (x : Cmd) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (cmdReadNames x s₁) -> proj₁ (oracle x) s ≡ proj₁ (oracle x) s₁
h₄ s s₁ x all₁ = sym (proj₂ (oracle x) s₁ s λ f₁ x₁ → sym (lookup all₁ x₁))

h₃ : {s s₁ : FileSystem} (x : Cmd) (xs ys : Build) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (buildReadNames s₁ (xs ++ x ∷ ys)) -> All (λ f₁ → script s xs f₁ ≡ script s₁ xs f₁) (cmdReadNames x (script s₁ xs))
h₃ {s} {s₁} x [] ys all₁ = ++⁻ˡ (cmdReadNames x s₁) all₁
h₃ {s} {s₁} x (x₁ ∷ xs) ys all₁ with ++⁻ (cmdReadNames x₁ s₁) all₁
... | all₂ , all₃ = h₃ {run x₁ s} {run x₁ s₁} x xs ys (lemma1-sym {s} {s₁} (buildReadNames (run x₁ s₁) (xs ++ x ∷ ys)) x₁ all₂ all₃)


h₁ : {s : FileSystem} (f₁ : FileName) -> (x w : Cmd) (xs ys ls₁ ls₂ : Build) -> f₁ ∈ cmdReadNames w (script s ls₁) -> Disjoint (cmdWriteNames x (script s xs)) (buildReadNames (run x (script s xs)) ys) -> xs ++ ys ≡ ls₁ ++ w ∷ ls₂ -> ∃[ ls₃ ](∃[ ls₄ ](xs ++ x ∷ ys ≡ ls₃ ++ w ∷ ls₄ × f₁ ∈ cmdReadNames w (script s ls₃)))
h₁ {s} f₁ x w [] ys ls₁ ls₂ f₁∈ dsj ys≡ls₁++w∷ls₂ with h₃ w ls₁ ls₂ (lemma5 (bs (ls₁ ++ w ∷ ls₂)) ws (subst (λ x₁ → Disjoint (map proj₁ ws) (bs x₁)) ys≡ls₁++w∷ls₂ dsj))
  where bs : Build -> List FileName
        bs b = buildReadNames (run x s) b
        ws : Files
        ws = proj₂ (proj₁ (oracle x) s)
... | all₂ = (x ∷ ls₁) , ls₂ , cong (x ∷_) ys≡ls₁++w∷ls₂ , subst (λ x₁ → f₁ ∈ x₁) (cong ((map proj₁) ∘ proj₁) (h₄ (script s ls₁) (script (run x s) ls₁) w all₂)) f₁∈
h₁ f₁ x w (x₁ ∷ xs) ys [] ls₂ f₁∈ dsj x₁∷xs++ys≡w∷ls₂ with ∷-injective x₁∷xs++ys≡w∷ls₂
... | x₁≡w , _ = [] , xs ++ x ∷ ys , cong₂ _∷_ x₁≡w refl , f₁∈
h₁ {s} f₁ x w (x₁ ∷ xs) ys (x₂ ∷ ls₁) ls₂ f₁∈ dsj x₁∷xs++ys≡x₂∷ls₁++w∷ls₂ with ∷-injective x₁∷xs++ys≡x₂∷ls₁++w∷ls₂
... | x₁≡x₂ , xs++ys≡ls₁++w∷ls₂ with h₁ {run x₂ s} f₁ x w xs ys ls₁ ls₂ f₁∈ dsj₂ xs++ys≡ls₁++w∷ls₂
  where dsj₂ : Disjoint (cmdWriteNames x (script (run x₂ s) xs)) (buildReadNames (run x (script (run x₂ s) xs)) ys)
        dsj₂ = λ x₃ → dsj (subst (λ x₄ → _ ∈ cmdWriteNames x (script (run x₄ s) xs)) (sym x₁≡x₂) (proj₁ x₃)
                          , subst (λ x₄ → _ ∈ buildReadNames (run x (script (run x₄ s) xs)) ys) (sym x₁≡x₂) (proj₂ x₃))
... | ls₃ , ls₄ , xs++x∷ys≡ls₃++w∷ls₄ , f₁∈₂ = x₂ ∷ ls₃ , ls₄ , cong₂ _∷_ x₁≡x₂ xs++x∷ys≡ls₃++w∷ls₄ , f₁∈₂

script-≡ : {sys sys₁ : FileSystem} (b : Build) -> (∀ f₁ → sys f₁ ≡ sys₁ f₁) -> (∀ f₁ → script sys b f₁ ≡ script sys₁ b f₁)
script-≡ [] ∀₁ f₁ = ∀₁ f₁
script-≡ (x ∷ b) ∀₁ = script-≡ b λ f₁ → run-≡ x ∀₁ f₁
\end{code}






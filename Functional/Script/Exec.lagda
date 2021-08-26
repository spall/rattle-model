\begin{code}[hide]
open import Functional.State as St using (F ; run ; System ; Cmd ; trace ; run-≡)

module Functional.Script.Exec (oracle : F) where

open import Common.List.Properties as CLP using (_before_en_ ; before-∷ʳ⁺)
open import Agda.Builtin.Equality
open import Data.Sum using (_⊎_)
open import Data.List using ([] ; _∷_ ; List ; map ; _++_ ; _∷ʳ_ ; [_] ; foldr ; reverse)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∄-syntax ; ∃-syntax ; Σ-syntax)

open import Functional.Build using (Build)
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

\newcommand{\exec}{%
\begin{code}
exec : System -> Build -> System
exec sys [] = sys
exec sys (x ∷ b) = exec (run oracle x sys) b
\end{code}}

\begin{code}[hide]
Cwrites : System -> Cmd -> List FileName
Cwrites s x = proj₂ (trace oracle s x)

Creads : System -> Cmd -> List FileName
Creads s x = proj₁ (trace oracle s x)

reads : System -> Build -> List FileName
reads _ [] = []
reads sys (x ∷ b) = (Creads sys x) ++ reads (run oracle x sys) b

writes : System -> Build -> List FileName
writes _ [] = []
writes sys (x ∷ b) = (Cwrites sys x) ++ writes (run oracle x sys) b

read-writes : System -> Cmd -> List FileName
read-writes sys c = let (rs , ws) = trace oracle sys c in
                        rs ++ ws

build-rws : System -> Build -> List FileName -> List FileName
build-rws sys [] ls = ls
build-rws sys (x ∷ b) ls = build-rws (run oracle x sys) b ((read-writes sys x) ++ ls)


-- proofs to go in own file eventually:        

-- use this instead of h₂
h₄ : (s s₁ : System) (x : Cmd) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (Creads s₁ x) -> proj₁ (oracle x) s ≡ proj₁ (oracle x) s₁
h₄ s s₁ x all₁ = sym (proj₂ (oracle x) s₁ s λ f₁ x₁ → sym (lookup all₁ x₁))

h₃ : {s s₁ : System} (x : Cmd) (xs ys : Build) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (reads s₁ (xs ++ x ∷ ys)) -> All (λ f₁ → exec s xs f₁ ≡ exec s₁ xs f₁) (Creads (exec s₁ xs) x)
h₃ {s} {s₁} x [] ys all₁ = ++⁻ˡ (Creads s₁ x) all₁
h₃ {s} {s₁} x (x₁ ∷ xs) ys all₁ with ++⁻ (Creads s₁ x₁) all₁
... | all₂ , all₃ = h₃ {run oracle x₁ s} {run oracle x₁ s₁} x xs ys (St.lemma1-sym {oracle} {s} {s₁} (reads (run oracle x₁ s₁) (xs ++ x ∷ ys)) x₁ all₂ all₃)


h₁ : {s : System} (f₁ : FileName) -> (x w : Cmd) (xs ys ls₁ ls₂ : Build) -> f₁ ∈ Creads (exec s ls₁) w -> Disjoint (Cwrites (exec s xs) x) (reads (run oracle x (exec s xs)) ys) -> xs ++ ys ≡ ls₁ ++ w ∷ ls₂ -> ∃[ ls₃ ](∃[ ls₄ ](xs ++ x ∷ ys ≡ ls₃ ++ w ∷ ls₄ × f₁ ∈ Creads (exec s ls₃) w))
h₁ {s} f₁ x w [] ys ls₁ ls₂ f₁∈ dsj ys≡ls₁++w∷ls₂ with h₃ w ls₁ ls₂ (St.lemma5 (bs (ls₁ ++ w ∷ ls₂)) ws (subst (λ x₁ → Disjoint (map proj₁ ws) (bs x₁)) ys≡ls₁++w∷ls₂ dsj))
  where bs : Build -> List FileName
        bs b = reads (run oracle x s) b
        ws : Files
        ws = proj₂ (proj₁ (oracle x) s)
... | all₂ = (x ∷ ls₁) , ls₂ , cong (x ∷_) ys≡ls₁++w∷ls₂ , subst (λ x₁ → f₁ ∈ x₁) (cong ((map proj₁) ∘ proj₁) (h₄ (exec s ls₁) (exec (run oracle x s) ls₁) w all₂)) f₁∈
h₁ f₁ x w (x₁ ∷ xs) ys [] ls₂ f₁∈ dsj x₁∷xs++ys≡w∷ls₂ with ∷-injective x₁∷xs++ys≡w∷ls₂
... | x₁≡w , _ = [] , xs ++ x ∷ ys , cong₂ _∷_ x₁≡w refl , f₁∈
h₁ {s} f₁ x w (x₁ ∷ xs) ys (x₂ ∷ ls₁) ls₂ f₁∈ dsj x₁∷xs++ys≡x₂∷ls₁++w∷ls₂ with ∷-injective x₁∷xs++ys≡x₂∷ls₁++w∷ls₂
... | x₁≡x₂ , xs++ys≡ls₁++w∷ls₂ with h₁ {run oracle x₂ s} f₁ x w xs ys ls₁ ls₂ f₁∈ dsj₂ xs++ys≡ls₁++w∷ls₂
  where dsj₂ : Disjoint (Cwrites (exec (run oracle x₂ s) xs) x) (reads (run oracle x (exec (run oracle x₂ s) xs)) ys)
        dsj₂ = λ x₃ → dsj (subst (λ x₄ → _ ∈ Cwrites (exec (run oracle x₄ s) xs) x) (sym x₁≡x₂) (proj₁ x₃)
                          , subst (λ x₄ → _ ∈ reads (run oracle x (exec (run oracle x₄ s) xs)) ys) (sym x₁≡x₂) (proj₂ x₃))
... | ls₃ , ls₄ , xs++x∷ys≡ls₃++w∷ls₄ , f₁∈₂ = x₂ ∷ ls₃ , ls₄ , cong₂ _∷_ x₁≡x₂ xs++x∷ys≡ls₃++w∷ls₄ , f₁∈₂

exec-≡ : {sys sys₁ : System} (b : Build) -> (∀ f₁ → sys f₁ ≡ sys₁ f₁) -> (∀ f₁ → exec sys b f₁ ≡ exec sys₁ b f₁)
exec-≡ [] ∀₁ f₁ = ∀₁ f₁
exec-≡ (x ∷ b) ∀₁ = exec-≡ b λ f₁ → run-≡ {oracle} x ∀₁ f₁
\end{code}






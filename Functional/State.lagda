
\begin{code}[hide]
module Functional.State where

open import Agda.Builtin.Equality
open import Data.Bool using (Bool ; if_then_else_)
open import Data.List using (List ; map ; foldr ; [] ; _∷_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ-syntax)
open import Data.String using (String ; _==_)
open import Data.String.Properties using (≡-setoid ; _≟_)
open import Functional.File using (File ; FileName ; FileContent ; Files)
open import Data.List.Membership.Setoid (≡-setoid) using (_∈_)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Relation.Binary.PropositionalEquality using (decSetoid ; trans ; sym ; subst)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈?_ ; _∉_)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Unary.Any using (here ; there ; tail)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
\end{code}

\newcommand{\sys}{%
\begin{code}
System : Set
System = FileName -> Maybe FileContent
\end{code}}

\newcommand{\cmd}{%
\begin{code}
Cmd : Set
Cmd = String
\end{code}}

\newcommand{\cmdF}{%
\begin{code}
CmdFunction : Set
CmdFunction = System → Files × Files
\end{code}}

\newcommand{\cmdP}{%
\begin{code}
CmdProof : CmdFunction → Set
CmdProof f = ∀ s₁ s₂ → (∀ f₁ → f₁ ∈ map proj₁ (proj₁ (f s₁)) -> s₁ f₁ ≡ s₂ f₁) -> f s₁ ≡ f s₂ 
\end{code}}

\newcommand{\oracle}{%
\begin{code}
F : Set
F = Cmd -> Σ[ f ∈ CmdFunction ](CmdProof)
\end{code}}

\newcommand{\mem}{%
\begin{code}
Memory : Set
Memory = List (Cmd × List (FileName × Maybe FileContent))
\end{code}}

\begin{code}[hide]
extend : File -> System -> System
extend (k , v) st = \ k₁ -> if (k == k₁) then just v else st k₁

read : List FileName -> System -> List (FileName × Maybe FileContent)
read fs sys = map (\ x -> (x , sys x)) fs

inputs : F -> System -> Cmd -> List FileName
inputs f sys cmd = map proj₁ (proj₁ (proj₁ (f cmd) sys))

trace : F -> System -> Cmd -> (List FileName × List FileName)
trace f sys cmd = let (rs , ws) = proj₁ (f cmd) sys in
                    (map proj₁ rs , map proj₁ ws)


run : F -> Cmd -> System -> System
run f cmd sys = foldr extend sys (proj₂ (proj₁ (f cmd) sys))


save : Cmd -> List FileName -> System -> Memory -> Memory
save cmd files sys mm = (cmd , map (\f -> f , sys f) files) ∷ mm

State : Set
State = (System × Memory) {- can add more later if needed -}

-- proofs --

{- if f₁ is in ls, then f₁ will be the same after both systems are extended with ls -}
lemma4 : {s s₁ : System} (ls : Files) -> (f₁ : FileName) -> f₁ ∈ map proj₁ ls -> foldr extend s ls f₁ ≡ foldr extend s₁ ls f₁
lemma4 ((f₂ , v₂) ∷ ls) f₁ f₁∈writes with f₂ ≟ f₁
... | yes f₂≡f₁ = refl
... | no ¬f₂≡f₁ = lemma4 ls f₁ (tail (λ f₁≡f₂ → ¬f₂≡f₁ (sym f₁≡f₂)) f₁∈writes)


{- if f₁ is not in ls then value of f₁ will be the same as in the original system after the system
   is extended with ls -}
lemma3 : {s : System} (f₁ : FileName) -> (ls : Files) -> f₁ ∉ map proj₁ ls -> s f₁ ≡ foldr extend s ls f₁
lemma3 f₁ [] f₁∉ = refl
lemma3 f₁ ((f₂ , v₂) ∷ ls) f₁∉ with f₂ ≟ f₁
... | yes f₂≡f₁ = contradiction (here (sym f₂≡f₁)) f₁∉
... | no ¬f₂≡f₂ = lemma3 f₁ ls (λ x → f₁∉ (there x))


{- if results of x are the same when run in 2 systems, and f₁ is the same in both systems, 
   then f₁ is the same in the new systems after running x in both systems
-}
lemma2 : {f : F} {s s₁ : System} (x : Cmd) -> (f₁ : FileName) -> proj₁ (f x) s ≡ proj₁ (f x) s₁ -> s f₁ ≡ s₁ f₁ -> run f x s f₁ ≡ run f x s₁ f₁
lemma2 {f} {s} {s₁} x f₁ result≡ s-f₁≡s₁-f₁ with f₁ ∈? proj₂ (trace f s x) -- is f₁ in writes of x
... | yes f₁∈writes
  = subst (λ x₁ → foldr extend s (proj₂ (proj₁ (f x) s)) f₁ ≡ foldr extend s₁ (proj₂ x₁) f₁)
          result≡
          (lemma4 {s} {s₁} (proj₂ (proj₁ (f x) s)) f₁ f₁∈writes)
lemma2 {f} {s} {s₁} x f₁ result≡ s-f₁≡s₁-f₁ | no f₁∉writes
  = trans (sym (lemma3 f₁ (proj₂ (proj₁ (f x) s)) f₁∉writes))
          (trans s-f₁≡s₁-f₁ (lemma3 f₁ (proj₂ (proj₁ (f x) s₁)) (subst (λ x₁ → f₁ ∉ map proj₁ (proj₂ x₁)) result≡ f₁∉writes)))


{- if x's inputs are the same in both systems then everything in ls will still be
   the same in the new systems after running x in both -}
lemma1 : {f : F} {s s₁ : System} (ls : List FileName) -> (x : Cmd) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (proj₁ (trace f s x)) -> All (λ f₁ → s f₁ ≡ s₁ f₁) ls -> All (λ f₁ → run f x s f₁ ≡ run f x s₁ f₁) ls
lemma1 [] x all₁ all₂ = All.[]
lemma1 {f} {s} {s₁} (f₁ ∷ ls) x all₁ (px All.∷ all₂) with proj₂ (f x) s s₁ (λ f₁ x₂ → lookup all₁ x₂)
... | result≡ = (lemma2 {f} {s} {s₁} x f₁ result≡ px) All.∷ (lemma1 {f} {s} {s₁} ls x all₁ all₂)

lemma1-sym : {f : F} {s s₁ : System} (ls : List FileName) -> (x : Cmd) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (proj₁ (trace f s₁ x)) -> All (λ f₁ → s f₁ ≡ s₁ f₁) ls -> All (λ f₁ → run f x s f₁ ≡ run f x s₁ f₁) ls
lemma1-sym [] x all₁ all₂ = All.[]
lemma1-sym {f} {s} {s₁} (x₁ ∷ ls) x all₁ (px All.∷ all₂) with proj₂ (f x) s₁ s λ f₁ x₂ → sym (lookup all₁ x₂)
... | result≡ = (lemma2 {f} {s} {s₁} x x₁ (sym result≡) px) All.∷ (lemma1-sym {f} {s} {s₁} ls x all₁ all₂)


lemma5 : {s : System} (ls : List FileName) (ls₁ : Files) -> Disjoint (map proj₁ ls₁) ls -> All (λ f₁ → s f₁ ≡ foldr extend s ls₁ f₁) ls
lemma5 [] ls₁ dsj = All.[]
lemma5 (x ∷ ls) ls₁ dsj with x ∈? map proj₁ ls₁
... | yes x∈ = contradiction (x∈ , here refl) dsj
... | no x∉ = (lemma3 x ls₁ x∉) All.∷ (lemma5 ls ls₁ λ x₁ → dsj (proj₁ x₁ , there (proj₂ x₁)))

run-≡ : {f : F} {sys sys₁ : System} (x : Cmd) -> (∀ f₁ → sys f₁ ≡ sys₁ f₁) -> (∀ f₁ → run f x sys f₁ ≡ run f x sys₁ f₁)
run-≡ {f} {sys} {sys₁} x ∀₁ f₁ = lemma2 {f} {sys} {sys₁} x f₁ ≡₁ (∀₁ f₁)
  where ≡₁ : proj₁ (f x) sys ≡ proj₁ (f x) sys₁
        ≡₁ = proj₂ (f x) sys sys₁ λ f₂ x₁ → ∀₁ f₂
  
\end{code}


open import Functional.State as St using (F ; System ; Memory ; Cmd ; trace ; extend)

module Functional.Forward.Properties (oracle : F) where

open import Data.Bool using (false ; if_then_else_)
open import Data.Product using (proj₁ ; proj₂ ; _,_)
open import Data.String using (String)
open import Agda.Builtin.Equality
open import Functional.File using (FileName ; FileContent ; Files)
open import Functional.Forward.Exec (oracle) using (run ; run? ; maybeAll ; get)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Maybe.Relation.Binary.Pointwise using (dec ; Pointwise)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Data.List using (List ; [] ; map ; foldr ; _∷_ ; _++_)
open import Relation.Nullary using (yes ; no)
open import Relation.Binary.PropositionalEquality using (decSetoid ; trans ; sym ; subst ; cong ; cong₂)
open import Data.Product using (_×_ ; ∃-syntax)
open import Data.List.Relation.Unary.All as All using (All ; all? ; lookup)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Function.Base using (_∘_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Data.List.Properties using (∷-injective)

open import Relation.Nullary.Negation using (contradiction)


-- running the cmd will have no effect on the state
CmdIdempotent : Cmd -> List (FileName × Maybe FileContent) -> System -> Set
CmdIdempotent x fs sys = All (λ (f₁ , v₁) → sys f₁ ≡ v₁) fs -> ∀ f₁ → St.run oracle x sys f₁ ≡ sys f₁

data IdempotentCmd : (Cmd -> System -> List FileName) -> Cmd -> List (FileName × Maybe FileContent) -> System -> Set where
 IC : {f : (Cmd -> System -> List FileName)} (x : Cmd) (fs : List (FileName × Maybe FileContent)) (sys : System) -> map proj₁ fs ≡ f x sys -> CmdIdempotent x fs sys -> IdempotentCmd f x fs sys

data IdempotentState : (Cmd -> System -> List FileName) -> System -> Memory -> Set where
  [] : {f : (Cmd -> System -> List FileName)} {s : System} -> IdempotentState f s []
  Cons : {f : (Cmd -> System -> List FileName)} {x : Cmd} {fs : List (FileName × Maybe FileContent)} {s : System} {mm : Memory} -> IdempotentCmd f x fs s -> IdempotentState f s mm -> IdempotentState f s ((x , fs) ∷ mm)

lemma1 : (f₁ : FileName) -> (ls : Files) -> f₁ ∈ map proj₁ ls -> ∃[ v ](∀ s → foldr extend s ls f₁ ≡ just v)
lemma1 f₁ ((f , v) ∷ ls) f₁∈ with f ≟ f₁
... | yes f≡f₁ = v , (λ s → refl)
... | no ¬f≡f₁ = lemma1 f₁ ls (tail (λ f≡f₁ → ¬f≡f₁ (sym f≡f₁)) f₁∈)


cmdIdempotent : (sys : System) (x : Cmd) -> Disjoint (proj₁ (trace oracle sys x)) (proj₂ (trace oracle sys x)) -> ∀ f₁ → St.run oracle x (St.run oracle x sys) f₁ ≡ St.run oracle x sys f₁
cmdIdempotent sys x dsj f₁ with proj₂ (oracle x) sys (St.run oracle x sys) λ f₂ x₁ → (St.lemma3 {sys} f₂ (proj₂ (proj₁ (oracle x) sys)) λ x₂ → dsj (x₁ , x₂))
... | ≡₁ with f₁ ∈? proj₂ (trace oracle sys x)
... | no f₁∉ = sym (St.lemma3 {foldr extend sys (proj₂ (proj₁ (oracle x) sys))} f₁ (proj₂ (proj₁ (oracle x) (foldr extend sys (proj₂ (proj₁ (oracle x) sys))))) (subst (λ x₁ → f₁ ∉ x₁) (cong ((map proj₁) ∘ proj₂) ≡₁) f₁∉))
... | yes f₁∈ with lemma1 f₁ (proj₂ (proj₁ (oracle x) sys)) f₁∈
... | v , ∀₁ with subst (λ x₁ → foldr extend (St.run oracle x sys) x₁ f₁ ≡ _) (cong proj₂ ≡₁) (∀₁ (St.run oracle x sys))
... | ≡₂ = trans ≡₂ (sym (∀₁ sys))


cmdWrites : Cmd -> System -> List FileName
cmdWrites x sys = map proj₁ (proj₂ (proj₁ (oracle x) sys))
cmdReads : Cmd -> System -> List FileName
cmdReads x sys = map proj₁ (proj₁ (proj₁ (oracle x) sys))
cmdReadWrites : Cmd -> System -> List FileName
cmdReadWrites x sys = (cmdReads x sys) ++ (cmdWrites x sys)

lemma2 : {sys : System} {ls : Files} (fs : List (FileName × Maybe FileContent)) -> All (λ (f₁ , v₁) → foldr extend sys ls f₁ ≡ v₁) fs -> Disjoint (map proj₁ fs) (map proj₁ ls) -> All (λ (f₁ , v₁) → sys f₁ ≡ v₁) fs
lemma2 [] all₁ dsj = All.[]
lemma2 {sys} {ls} ((f₁ , v₁) ∷ fs) (px All.∷ all₁) dsj = (trans (St.lemma3 f₁ ls λ x → dsj (here refl , x)) px) All.∷ (lemma2 fs all₁ λ x₁ → dsj (there (proj₁ x₁) , proj₂ x₁))

∈-resp-≡ : {ls ls₁ : List String} {v : String} -> v ∈ ls -> ls ≡ ls₁ -> v ∈ ls₁
∈-resp-≡ v∈ls ls≡ls₁ = subst (λ x → _ ∈ x) ls≡ls₁ v∈ls

runPreserves : {sys : System} (x x₁ : Cmd) -> (fs : List (FileName × Maybe FileContent)) -> Disjoint (cmdWrites x₁ sys) (cmdReadWrites x sys) -> IdempotentCmd cmdReads x fs sys -> IdempotentCmd cmdReads x fs (St.run oracle x₁ sys)
runPreserves {sys} x x₁ fs dsj (IC .x .fs .sys x₂ ci) = IC x fs (St.run oracle x₁ sys) ≡₁ λ all₁ f₁ → ≡₂ f₁ all₁
  where ≡₀ : proj₁ (oracle x) (St.run oracle x₁ sys) ≡ proj₁ (oracle x) sys
        ≡₀ = sym (proj₂ (oracle x) sys (St.run oracle x₁ sys) λ f₁ x₃ → St.lemma3 f₁ (proj₂ (proj₁ (oracle x₁) sys)) λ x₄ → dsj (x₄ , ∈-++⁺ˡ x₃))
        ≡₁ : map proj₁ fs ≡ cmdReads x (St.run oracle x₁ sys)
        ≡₁ = trans x₂ (sym (cong (map proj₁ ∘ proj₁) ≡₀))
        ≡₂ : (f₁ : FileName) -> All (λ (f₁ , v₁) → St.run oracle x₁ sys f₁ ≡ v₁) fs -> St.run oracle x (St.run oracle x₁ sys) f₁ ≡ St.run oracle x₁ sys f₁
        ≡₂ f₁ all₁ with f₁ ∈? cmdWrites x (St.run oracle x₁ sys)
        ... | no f₁∉ = sym (St.lemma3 f₁ (proj₂ (proj₁ (oracle x) (St.run oracle x₁ sys))) f₁∉)
        ... | yes f₁∈ with f₁ ∈? cmdWrites x₁ sys
        ... | yes f₁∈₁ = contradiction (f₁∈₁ , ∈-++⁺ʳ _ (∈-resp-≡ f₁∈ (cong (map proj₁ ∘ proj₂) ≡₀))) dsj
        ... | no f₁∉ = trans (trans (St.lemma4 {St.run oracle x₁ sys} {sys} (proj₂ (proj₁ (oracle x) (St.run oracle x₁ sys))) f₁ f₁∈) (cong₂ (foldr extend sys ∘ proj₂) ≡₀ refl))
                             (trans (ci (lemma2 fs all₁ λ x₃ → dsj (proj₂ x₃ , ∈-++⁺ˡ (∈-resp-≡ (proj₁ x₃) x₂))) f₁) (St.lemma3 f₁ (proj₂ (proj₁ (oracle x₁) sys)) f₁∉))


preserves2 : {sys : System} {mm : Memory} (x : Cmd) -> IdempotentState cmdReads sys mm -> All (λ x₁ → Disjoint (cmdWrites x sys) (cmdReadWrites x₁ sys)) (map proj₁ mm) -> IdempotentState cmdReads (St.run oracle x sys) mm
preserves2 x [] all₁ = []
preserves2 {sys} {(x₅ , _) ∷ mm} x (Cons ic is) (px All.∷ all₁) = Cons (runPreserves x₅ x _ px ic) (preserves2 x is all₁)


preserves : {sys : System} {mm : Memory} (x : Cmd) -> Disjoint (proj₁ (trace oracle sys x)) (proj₂ (trace oracle sys x)) -> All (λ x₁ → Disjoint (cmdWrites x sys) (cmdReadWrites x₁ sys)) (map proj₁ mm) -> IdempotentState cmdReads sys mm -> IdempotentState cmdReads (St.run oracle x sys) (St.save x (proj₁ (trace oracle sys x)) (St.run oracle x sys) mm)
preserves {sys} x dsj all₁ is = Cons ic (preserves2 x is all₁)
  where g₁ : (xs ys : List FileName) -> xs ≡ ys -> map proj₁ (map (λ f → f , St.run oracle x sys f) xs) ≡ ys
        g₁ [] ys ≡₁ = ≡₁
        g₁ (x ∷ xs) (x₁ ∷ ys) ≡₁ with ∷-injective ≡₁
        ... | x≡x₁ , xs≡ys = cong₂ _∷_ x≡x₁ (g₁ xs ys xs≡ys)
        g₂ : proj₁ (trace oracle sys x) ≡ proj₁ (trace oracle (St.run oracle x sys) x)
        g₂ with proj₂ (oracle x) sys (St.run oracle x sys) λ f₁ x₁ → (St.lemma3 f₁ (proj₂ (proj₁ (oracle x) sys)) λ x₂ → dsj (x₁ , x₂))
        ... | ≡₁ = cong (map proj₁ ∘ proj₁) ≡₁
        ic : IdempotentCmd cmdReads x (map (λ f → f , St.run oracle x sys f) (cmdReads x sys)) (St.run oracle x sys)
        ic = IC x (map (λ f → f , St.run oracle x sys f) (cmdReads x sys))
                  (St.run oracle x sys)
                  (g₁ (cmdReads x sys) (cmdReads x (St.run oracle x sys)) (g₂))
                  λ _ → cmdIdempotent sys x dsj

getCmdIdempotent : {f : (Cmd -> System -> List FileName)} {sys : System} (mm : Memory) (x : Cmd) -> IdempotentState f sys mm -> (x∈ : x ∈ map proj₁ mm) -> CmdIdempotent x (get x mm x∈) sys
getCmdIdempotent ((x₁ , fs) ∷ mm) x (Cons (IC .x₁ .fs _ ≡₂ x₃) is) x∈ with x ≟ x₁
... | yes x≡x₁ = subst (λ x₂ → CmdIdempotent x₂ _ _) (sym x≡x₁) x₃
... | no ¬x≡x₁ = getCmdIdempotent mm x is (tail ¬x≡x₁ x∈)


run≡ : (sys₁ sys₂ : System) (mm : Memory) (x : Cmd) -> (∀ f₁ → sys₁ f₁ ≡ sys₂ f₁) -> IdempotentState cmdReads sys₂ mm -> ∀ f₁ → St.run oracle x sys₁ f₁ ≡ proj₁ (run (sys₂ , mm) x) f₁
run≡ sys₁ sys₂ mm x ∀₁ is f₁ with x ∈? map proj₁ mm
... | no x∉ = St.lemma2 {oracle} {sys₁} {sys₂} x f₁ (proj₂ (oracle x) sys₁ sys₂ λ f₂ _ → ∀₁ f₂) (∀₁ f₁)
... | yes x∈ with maybeAll {sys₂} (get x mm x∈)
... | nothing = St.lemma2 {oracle} {sys₁} {sys₂} x f₁ (proj₂ (oracle x) sys₁ sys₂ λ f₂ _ → ∀₁ f₂) (∀₁ f₁)
... | just all₁ with getCmdIdempotent mm x is x∈
... | ci = trans (St.lemma2 {oracle} {sys₁} {sys₂} x f₁ (proj₂ (oracle x) sys₁ sys₂ λ f₂ _ → ∀₁ f₂) (∀₁ f₁))
                        (ci all₁ f₁)

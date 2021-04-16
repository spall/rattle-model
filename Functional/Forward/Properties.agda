-- {-# OPTIONS --allow-unsolved-metas #-}

open import Functional.State as St using (F ; System ; Memory ; Cmd ; trace ; extend)

module Functional.Forward.Properties (oracle : F) where

open import Data.Bool using (false ; if_then_else_)
open import Data.Product using (proj₁ ; proj₂ ; _,_)
open import Agda.Builtin.Equality
open import Functional.File using (FileName ; FileContent ; Files)
open import Functional.Forward.Exec (oracle) using (run ; run? ; maybeAll ; get)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Maybe.Relation.Binary.Pointwise using (dec ; Pointwise)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Data.List using (List ; [] ; map ; foldr ; _∷_ ; _++_)
open import Relation.Nullary using (yes ; no)
open import Relation.Binary.PropositionalEquality using (decSetoid ; trans ; sym ; subst ; cong)
open import Data.Product using (_×_ ; ∃-syntax)
open import Data.List.Relation.Unary.All as All using (All ; all? ; lookup)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Function.Base using (_∘_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)

open import Relation.Nullary.Negation using (contradiction)


-- running the cmd will have no effect on the state
CmdIdempotent : Cmd -> List (FileName × Maybe FileContent) -> System -> Set
CmdIdempotent x fs sys = All (λ (f₁ , v₁) → sys f₁ ≡ v₁) fs -> ∀ f₁ → St.run oracle x sys f₁ ≡ sys f₁
-- map proj₁ fs ≡ map proj₁ (proj₁ (proj₁ (oracle x) sys))
-- All (λ (f₁ , v₁) → sys f₁ ≡ just v₁) (proj₂ (proj₁ (oracle x) sys))


inputs : System -> Cmd -> List (FileName × Maybe FileContent)
inputs s x = map (\f → f , St.run oracle x s f) (proj₁ (trace oracle s x))

data IdempotentCmd : Cmd -> List (FileName × Maybe FileContent) -> System -> Set where
 IC : (x : Cmd) (fs : List (FileName × Maybe FileContent)) (sys : System) -> map proj₁ fs ≡ map proj₁ (proj₁ (proj₁ (oracle x) sys)) -> CmdIdempotent x fs sys -> IdempotentCmd x fs sys

data IdempotentState : System -> Memory -> Set where
  [] : {s : System} -> IdempotentState s []
  Cons : {x : Cmd} {fs : List (FileName × Maybe FileContent)} {s : System} {mm : Memory} -> map proj₁ fs ≡ proj₁ (trace oracle s x) -> CmdIdempotent x fs s -> IdempotentState s mm -> IdempotentState s ((x , fs) ∷ mm)

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

lemma3 : (sys : System) (x x₁ : Cmd) -> Disjoint (cmdReads x sys) (cmdWrites x₁ sys) -> proj₁ (oracle x) sys ≡ proj₁ (oracle x) (St.run oracle x₁ sys)
lemma3 sys x x₁ dsj = proj₂ (oracle x) sys (St.run oracle x₁ sys) λ f₁ x₂ → (St.lemma3 f₁ (proj₂ (proj₁ (oracle x₁) sys)) λ x₃ → dsj (x₂ , x₃))


runPreserves : {sys : System} (x x₁ : Cmd) -> (fs : List (FileName × Maybe FileContent)) -> map proj₁ fs ≡ map proj₁ (proj₁ (proj₁ (oracle x) sys)) -> Disjoint (cmdWrites x₁ sys) (cmdReadWrites x sys) -> CmdIdempotent x fs sys -> CmdIdempotent x fs (St.run oracle x₁ sys)
runPreserves {sys} x₀ x₁ fs x₃ dsj ip with sym (lemma3 sys x₀ x₁ λ x₂ → dsj ((proj₂ x₂) , ∈-++⁺ˡ (proj₁ x₂)))
... | ≡₁ with cong (map proj₁ ∘ proj₂) ≡₁ | cong (map proj₁ ∘ proj₁) ≡₁ | sym (cong proj₂ ≡₁)
... | ≡₂ | ≡₃ | ≡₄ = λ x₂ f₁ → g₁ f₁ (ip (g₂ fs x₂ λ x → dsj (proj₂ x , ∈-++⁺ˡ (subst (λ x₄ → _ ∈ x₄) x₃ (proj₁ x)))) f₁)
  where g₁ : (f₁ : FileName) -> St.run oracle x₀ sys f₁ ≡ sys f₁ -> St.run oracle x₀ (St.run oracle x₁ sys) f₁ ≡ St.run oracle x₁ sys f₁
        g₁ f₁ ≡₅ with f₁ ∈? cmdWrites x₀ (St.run oracle x₁ sys)
        ... | no f₁∉ = (sym (St.lemma3 f₁ (proj₂ (proj₁ (oracle x₀) (St.run oracle x₁ sys))) f₁∉))
        ... | yes f₁∈ with f₁ ∈? cmdWrites x₁ sys
        ... | yes f₁∈₁ = contradiction (f₁∈₁ , ∈-++⁺ʳ (cmdReads x₀ sys) (subst (λ x → f₁ ∈ x) ≡₂ f₁∈)) dsj
        ... | no f₁∉₁ with St.lemma4 {St.run oracle x₁ sys} {sys} (proj₂ (proj₁ (oracle x₀) (St.run oracle x₁ sys))) f₁ f₁∈
        ... | ≡₁ with subst (λ x → foldr extend (St.run oracle x₁ sys) (proj₂ (proj₁ (oracle x₀) (St.run oracle x₁ sys))) f₁ ≡ foldr extend sys x f₁) (sym ≡₄) ≡₁
        ... | ≡₂ = trans ≡₂ (trans ≡₅ (St.lemma3 f₁ (proj₂ (proj₁ (oracle x₁) sys)) f₁∉₁))
        g₂ : (fs : List (FileName × Maybe FileContent)) -> All (λ (f₁ , v₁) → St.run oracle x₁ sys f₁ ≡ v₁) fs -> Disjoint (map proj₁ fs) (map proj₁ (proj₂ (proj₁ (oracle x₁) sys))) -> All (λ (f₁ , v₁) → sys f₁ ≡ v₁) fs
        g₂ [] all₁ dsj = All.[]
        g₂ (x ∷ fs) all₁ dsj with lookup all₁ (here refl)
        ... | ≡₁ = (trans (St.lemma3 (proj₁ x) (proj₂ (proj₁ (oracle x₁) sys)) λ x₃ → dsj (here refl , x₃)) ≡₁) All.∷ (g₂ fs (All.tail all₁) λ x₃ → dsj (there (proj₁ x₃) , proj₂ x₃))


-- todo: prove
-- IdempotentState sys mm -> IdempotentState (St.run oracle x sys) mm
-- knowing that x doesnt write to anything commands in mm read/wrote ; do i have that evidence tho?
preserves2 : {sys : System} {mm : Memory} (x : Cmd) -> IdempotentState sys mm -> All (λ x₁ → Disjoint (cmdWrites x sys) (cmdReadWrites x₁ sys)) (map proj₁ mm) -> IdempotentState (St.run oracle x sys) mm
preserves2 x [] all₁ = []
preserves2 {sys} {(x₅ , _) ∷ mm} x (Cons ≡₁ x₁ is) all₁ = Cons (trans ≡₁ (g₁)) (runPreserves _ x _ ≡₁ (lookup all₁ (here refl)) x₁) (preserves2 x is (All.tail all₁))
  where g₁ : proj₁ (trace oracle sys x₅) ≡ proj₁ (trace oracle (St.run oracle x sys) x₅)
        g₁ with proj₂ (oracle x₅) sys (St.run oracle x sys) λ f₁ x₄ → (St.lemma3 f₁ (proj₂ (proj₁ (oracle x) sys)) λ x₃ → (lookup all₁ (here refl)) (x₃ , ∈-++⁺ˡ x₄))
        ... | ≡₁ = cong (map proj₁ ∘ proj₁) ≡₁


preserves : {sys : System} {mm : Memory} (x : Cmd) -> Disjoint (proj₁ (trace oracle sys x)) (proj₂ (trace oracle sys x)) -> All (λ x₁ → Disjoint (cmdWrites x sys) (cmdReadWrites x₁ sys)) (map proj₁ mm) -> IdempotentState sys mm -> IdempotentState (St.run oracle x sys) (St.save x (proj₁ (trace oracle sys x)) (St.run oracle x sys) mm)
preserves {sys} x dsj all₁ is = Cons (subst (λ x₁ → map proj₁ (map (λ f → f , St.run oracle x sys f) (proj₁ (trace oracle sys x))) ≡ x₁) (g₂) (g₁ (proj₁ (trace oracle sys x)))) (λ _ → cmdIdempotent sys x dsj) (preserves2 x is all₁)
  where g₁ : (ls : List FileName) -> map proj₁ (map (λ f → f , St.run oracle x sys f) ls) ≡ ls
        g₁ [] = refl
        g₁ (x ∷ ls) = cong (x ∷_) (g₁ ls)
        g₂ : proj₁ (trace oracle sys x) ≡ proj₁ (trace oracle (St.run oracle x sys) x)
        g₂ with proj₂ (oracle x) sys (St.run oracle x sys) λ f₁ x₁ → (St.lemma3 f₁ (proj₂ (proj₁ (oracle x) sys)) λ x₂ → dsj (x₁ , x₂))
        ... | ≡₁ = cong (map proj₁ ∘ proj₁) ≡₁
        
{- We know that for the list ls, which is the list of files already read/written to that the value of those files will not change after a new cmd is run. 

-}

{- we know that the files that cmd is oging to write to are disjoint from a certain set of files, which sould be the fil
-}
-- lemma1 : (sys : System) -> (mm : Memory) -> (cmd : Cmd) -> (∀ x → run? x (sys , mm) ≡ false -> ∀ f₁ → St.run oracle x sys f₁ ≡ sys f₁) -> (∀ x → run? x (run (sys , mm) cmd) ≡ false -> ∀ f₁ → St.run oracle x (proj₁ (run (sys , mm) cmd)) f₁ ≡ (proj₁ (run (sys , mm) cmd)) f₁)

-- lemma1 : All (λ f₁ → sys f₁ ≡ St.run oracle x sys f₁) ls

{- goal: if cmd is in memory then there exists a cmdidempotent. 

-}
getCmdIdempotent : {sys : System} (mm : Memory) (x : Cmd) -> IdempotentState sys mm -> (x∈ : x ∈ map proj₁ mm) -> CmdIdempotent x (get x mm x∈) sys
getCmdIdempotent ((x₁ , fs) ∷ mm) x (Cons ≡₁ x₂ is) x∈ with x ≟ x₁
... | yes x≡x₁ = subst (λ x₃ → CmdIdempotent x₃ _ _) (sym x≡x₁) x₂
... | no ¬x≡x₁ = getCmdIdempotent mm x is (tail ¬x≡x₁ x∈)


run≡ : (sys₁ sys₂ : System) (mm : Memory) (x : Cmd) -> (∀ f₁ → sys₁ f₁ ≡ sys₂ f₁) -> IdempotentState sys₂ mm -> ∀ f₁ → St.run oracle x sys₁ f₁ ≡ proj₁ (run (sys₂ , mm) x) f₁
run≡ sys₁ sys₂ mm x ∀₁ is f₁ with x ∈? map proj₁ mm
... | no x∉ = St.lemma2 {oracle} {sys₁} {sys₂} x f₁ (proj₂ (oracle x) sys₁ sys₂ λ f₂ _ → ∀₁ f₂) (∀₁ f₁)
... | yes x∈ with maybeAll {sys₂} (get x mm x∈)
... | nothing = St.lemma2 {oracle} {sys₁} {sys₂} x f₁ (proj₂ (oracle x) sys₁ sys₂ λ f₂ _ → ∀₁ f₂) (∀₁ f₁)
... | just all₁ with getCmdIdempotent mm x is x∈
... | ci = trans (St.lemma2 {oracle} {sys₁} {sys₂} x f₁ (proj₂ (oracle x) sys₁ sys₂ λ f₂ _ → ∀₁ f₂) (∀₁ f₁))
                        (ci all₁ f₁)


{- with dec _≡?_ (changed? x (sys₂ , mm)) (just [])
  ... | yes a = trans (St.lemma2 {oracle} {sys₁} {sys₂} x f₁ (proj₂ (oracle x) sys₁ sys₂ (λ f₂ x₁ → ∀₁ f₂)) (∀₁ f₁)) (∀₂ a f₁)
... | no a = St.lemma2 {oracle} {sys₁} {sys₂} x f₁ (proj₂ (oracle x) sys₁ sys₂ (λ f₂ x₁ → ∀₁ f₂)) (∀₁ f₁)
-}

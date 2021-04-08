
open import Functional.State as St using (State ; F ; Cmd ; save ; System ; trace ; Memory ; extend)

module Functional.Forward.Exec (oracle : F) where

open import Agda.Builtin.Equality
open import Data.Bool using (Bool ; if_then_else_)
open import Data.List using (List ; [] ; _∷_ ; map ; filter ; foldr ; _++_)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Data.Maybe as Maybe using (Maybe ; just)
open import Data.Maybe.Relation.Binary.Pointwise using (dec)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∃-syntax)
open import Function.Base using (_∘_)
open import Functional.File using (FileName ; FileContent ; Files)
open import Functional.Build using (Build)
open import Relation.Nullary.Decidable.Core using (isNo)
open import Relation.Nullary.Negation using (¬?)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Data.List.Relation.Unary.All as All using (All ; all? ; lookup)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Relation.Binary.PropositionalEquality using (decSetoid ; trans ; sym ; subst ; cong)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (Any-resp-⊆ ; ⊆-reflexive)

{- we want to say that if a command is in the memory; and the values of its inputs are up to date; then running the command will have no effect
-}

-- running the cmd will have no effect on the state
CmdIdempotent : Cmd -> List (FileName × Maybe FileContent) -> System -> Set
CmdIdempotent x fs sys = All (λ (f₁ , v₁) → sys f₁ ≡ v₁) fs -> map proj₁ fs ≡ map proj₁ (proj₁ (proj₁ (oracle x) sys)) -> All (λ (f₁ , v₁) → sys f₁ ≡ just v₁) (proj₂ (proj₁ (oracle x) sys))


inputs : System -> Cmd -> List (FileName × Maybe FileContent)
inputs s x = map (\f → f , St.run oracle x s f) (proj₁ (trace oracle s x))

data IdempotentState : System -> Memory -> Set where
  [] : {s : System} -> IdempotentState s []
  _∷_ : {x : Cmd} {s : System} {mm : Memory} {fs : List (FileName × Maybe FileContent)} -> CmdIdempotent x fs s -> IdempotentState s mm -> IdempotentState s ((x , fs) ∷ mm)


lemma1 : (f₁ : FileName) -> (ls : Files) -> f₁ ∈ map proj₁ ls -> ∃[ v ](∀ s → foldr extend s ls f₁ ≡ just v)
lemma1 f₁ ((f , v) ∷ ls) f₁∈ with f ≟ f₁
... | yes f≡f₁ = v , (λ s → refl)
... | no ¬f≡f₁ = lemma1 f₁ ls (tail (λ f≡f₁ → ¬f≡f₁ (sym f≡f₁)) f₁∈)


{- this is true if? all of the writes of x are already in sys₁ -}
-- problem is we don't know where the v₁ occurs in ls
lemma2 : {sys₁ : System} (x : Cmd) (ls : Files) -> All (λ (f₁ , v₁) → sys₁ f₁ ≡ just v₁) ls -> ∀ f₁ → foldr extend sys₁ ls f₁ ≡ sys₁ f₁
lemma2 {sys₁} x ls all₁ f₁ with f₁ ∈? map proj₁ ls
... | no f₁∉ = sym (St.lemma3 f₁ ls f₁∉)
... | yes f₁∈ with lemma1 f₁ ls f₁∈
... | v , ∀₁ = trans (∀₁ sys₁) (sym (lookup all₁ {!!}))


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

runPreserves : {sys : System} (x x₁ : Cmd) -> (fs : List (FileName × Maybe FileContent)) -> Disjoint (cmdWrites x₁ sys) (cmdReadWrites x sys) -> CmdIdempotent x fs sys -> CmdIdempotent x fs (St.run oracle x₁ sys)
runPreserves {sys} x₀ x₁ fs dsj ip with sym (lemma3 sys x₀ x₁ λ x₂ → dsj ((proj₂ x₂) , ∈-++⁺ˡ (proj₁ x₂)))
... | ≡₁ with cong (map proj₁ ∘ proj₂) ≡₁ | cong (map proj₁ ∘ proj₁) ≡₁ | sym (cong proj₂ ≡₁)
... | ≡₂ | ≡₃ | ≡₄ = λ x₂ x₃ → g₁ (proj₂ (proj₁ (oracle x₀) (St.run oracle x₁ sys))) x₂ (subst (λ x → All _ x) ≡₄ (ip (g₂ fs x₂ λ x → dsj ((proj₂ x) , ∈-++⁺ˡ (subst (λ x₄ → _ ∈ x₄) (trans x₃ ≡₃) (proj₁ x)))) (trans x₃ ≡₃))) (⊆-reflexive ≡₂)

  where g₂ : (fs : List (FileName × Maybe FileContent)) -> All (λ (f₁ , v₁) → St.run oracle x₁ sys f₁ ≡ v₁) fs -> Disjoint (map proj₁ fs) (map proj₁ (proj₂ (proj₁ (oracle x₁) sys))) -> All (λ (f₁ , v₁) → sys f₁ ≡ v₁) fs
        g₂ [] all₁ dsj = All.[]
        g₂ (x ∷ fs) all₁ dsj with lookup all₁ (here refl)
        ... | ≡₁ = (trans (St.lemma3 (proj₁ x) (proj₂ (proj₁ (oracle x₁) sys)) λ x₃ → dsj (here refl , x₃)) ≡₁) All.∷ (g₂ fs (All.tail all₁) λ x₃ → dsj (there (proj₁ x₃) , proj₂ x₃))
        
        g₁ : (ls : Files) -> All (λ (f₁ , v₁) → St.run oracle x₁ sys f₁ ≡ v₁) fs -> All (λ (f₁ , v₁) → sys f₁ ≡ just v₁) ls -> map proj₁ ls ⊆ map proj₁ (proj₂ (proj₁ (oracle x₀) sys)) -> All (λ (f₁ , v₁) → St.run oracle x₁ sys f₁ ≡ just v₁) ls
        g₁ [] all₁ all₂ ls⊆ = All.[]
        g₁ (x ∷ ls) all₁ all₂ ls⊆ with Any-resp-⊆ ls⊆ (here refl)
        ... | ∈₁ = (trans (sym (St.lemma3 _ (proj₂ (proj₁ (oracle x₁) sys)) λ x₂ → dsj (x₂ , ∈-++⁺ʳ (cmdReads x₀ sys) ∈₁))) (lookup all₂ (here refl))) All.∷ (g₁ ls all₁ (All.tail all₂) λ x₂ → Any-resp-⊆ ls⊆ (there x₂))

-- todo: prove
-- IdempotentState sys mm -> IdempotentState (St.run oracle x sys) mm
-- knowing that x doesnt write to anything commands in mm read/wrote ; do i have that evidence tho?
preserves2 : {sys : System} {mm : Memory} (x : Cmd) -> IdempotentState sys mm -> IdempotentState (St.run oracle x sys) mm
preserves2 x [] = []
preserves2 x (x₁ ∷ is) = {!!} ∷ {!!}


preserves : {sys : System} {mm : Memory} (x : Cmd) -> Disjoint (proj₁ (trace oracle sys x)) (proj₂ (trace oracle sys x)) -> IdempotentState sys mm -> IdempotentState (St.run oracle x sys) (St.save x (proj₁ (trace oracle sys x)) sys mm)
preserves {sys} x dsj [] = (λ x₁ x₂ → {!!})  ∷ [] -- (λ x₁ f₁ → cmdIdempotent sys x dsj f₁) ∷ []
preserves {sys} x dsj (x₁ ∷ is) = {!!} ∷ {!!} -- (λ x₃ f₁ → cmdIdempotent sys x dsj f₁) ∷ {!!}


run? : Cmd -> State -> Bool
run? cmd (sys , []) = Bool.true
run? cmd (sys , (x₁ , fs) ∷ mm) = if cmd == x₁
                                  then isNo (all? (λ (f₁ , v₁) → dec _≟_ (sys f₁) v₁) fs)
                                  else run? cmd (sys , mm)

run : State -> Cmd -> State
run st cmd = if (run? cmd st)
               then (let sys = St.run oracle cmd (proj₁ st) in
                       (sys , save cmd (proj₁ (trace oracle (proj₁ st) cmd)) sys (proj₂ st)))
               else st


exec : State -> Build -> State
exec st [] = st
exec st (x ∷ b) = exec (run st x) b

{- Goal: prove if a command is in the memory, and the recorded files and the values of the files in the system are the same as the values in the memory, then
   running the command is equivalent to not running the command. 

 Or similarly/equivalently if a command is in the memory and the recorded files match what is in the system, then the files/values that the oracle says would be the output files, are already in the system. 

What does it mean for the command to be in the memory? The command is in the memory list, so it has
a corresponding list of files and maybe file contents, which in the case of the forward build, are
the files and their values read by the ocmmand when it was recorded as being run.  




-}

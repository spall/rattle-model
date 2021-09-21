
\begin{code}[hide]
{-# OPTIONS --allow-unsolved-metas #-}
open import Functional.State using (F ; System ; Memory ; Cmd ; extend ; save)

module Functional.Forward.Properties (oracle : F) where

open import Functional.State.Helpers (oracle) as St hiding (run)
open import Functional.State.Properties (oracle) as StP using (lemma3 ; lemma4 ; run-≡)
open import Data.Bool using (false ; if_then_else_)
open import Data.Product using (proj₁ ; proj₂ ; _,_)
open import Data.String using (String)
open import Agda.Builtin.Equality
open import Functional.File using (FileName ; FileContent ; Files)
open import Functional.Script.Exec (oracle) using (script)
open import Functional.Forward.Exec (oracle) using (run ; run? ; maybeAll ; get ; forward)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Maybe.Relation.Binary.Pointwise using (dec ; Pointwise)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)
open import Data.List using (List ; [] ; map ; foldr ; _∷_ ; _++_ ; concatMap)
open import Relation.Nullary using (yes ; no)
open import Relation.Binary.PropositionalEquality using (decSetoid ; trans ; sym ; subst ; cong ; cong₂)
open import Data.Product using (_×_ ; ∃-syntax)
open import Data.List.Relation.Unary.All as All using (All ; all? ; lookup)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Function.Base using (_∘_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-++⁻)
open import Data.List.Properties using (∷-injective)
open import Functional.Script.Hazard (oracle) using (HazardFree ; :: ; files ; filesRead; Hazard ; ReadWrite ; WriteWrite) renaming (save to rec)
open import Functional.Script.Hazard.Properties (oracle) using (hf-still) renaming (g₂ to ∉toAll)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Functional.Script.Properties (oracle) using (DisjointBuild ; Cons ; dsj-≡)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import Relation.Nullary.Negation using (contradiction)


-- running the cmd will have no effect on the state
CmdIdempotent : Cmd -> List (FileName × Maybe FileContent) -> System -> Set
CmdIdempotent x fs sys = All (λ (f₁ , v₁) → sys f₁ ≡ v₁) fs -> ∀ f₁ → St.run x sys f₁ ≡ sys f₁

data IdempotentCmd : (Cmd -> System -> List FileName) -> Cmd -> List (FileName × Maybe FileContent) -> System -> Set where
 IC : {f : (Cmd -> System -> List FileName)} (x : Cmd) (fs : List (FileName × Maybe FileContent)) (sys : System) -> map proj₁ fs ≡ f x sys -> CmdIdempotent x fs sys -> IdempotentCmd f x fs sys

data IdempotentState : (Cmd -> System -> List FileName) -> System -> Memory -> Set where
  [] : {f : (Cmd -> System -> List FileName)} {s : System} -> IdempotentState f s []
  Cons : {f : (Cmd -> System -> List FileName)} {x : Cmd} {fs : List (FileName × Maybe FileContent)} {s : System} {mm : Memory} -> IdempotentCmd f x fs s -> IdempotentState f s mm -> IdempotentState f s ((x , fs) ∷ mm)

lemma1 : (f₁ : FileName) -> (ls : Files) -> f₁ ∈ map proj₁ ls -> ∃[ v ](∀ s → foldr extend s ls f₁ ≡ just v)
lemma1 f₁ ((f , v) ∷ ls) f₁∈ with f ≟ f₁
... | yes f≡f₁ = v , (λ s → refl)
... | no ¬f≡f₁ = lemma1 f₁ ls (tail (λ f≡f₁ → ¬f≡f₁ (sym f≡f₁)) f₁∈)


cmdIdempotent : (sys : System) (x : Cmd) -> Disjoint (cmdReadNames x sys) (cmdWriteNames x sys) -> ∀ f₁ → St.run x (St.run x sys) f₁ ≡ St.run x sys f₁
cmdIdempotent sys x dsj f₁ with proj₂ (oracle x) sys (St.run x sys) (λ f₂ x₁ → (lemma3 {sys} f₂ (proj₂ (proj₁ (oracle x) sys)) λ x₂ → dsj (x₁ , x₂)))
... | ≡₁ with f₁ ∈? cmdWriteNames x sys
... | no f₁∉ = sym (lemma3 {foldr extend sys (proj₂ (proj₁ (oracle x) sys))} f₁ (proj₂ (proj₁ (oracle x) (foldr extend sys (proj₂ (proj₁ (oracle x) sys))))) (subst (λ x₁ → f₁ ∉ x₁) (cong ((map proj₁) ∘ proj₂) ≡₁) f₁∉))
... | yes f₁∈ with lemma1 f₁ (proj₂ (proj₁ (oracle x) sys)) f₁∈
... | v , ∀₁ with subst (λ x₁ → foldr extend (St.run x sys) x₁ f₁ ≡ _) (cong proj₂ ≡₁) (∀₁ (St.run x sys))
... | ≡₂ = trans ≡₂ (sym (∀₁ sys))

cmdReadWrites : Cmd -> System -> List FileName
cmdReadWrites x sys = (cmdReadNames x sys) ++ (cmdWriteNames x sys)

lemma2 : {sys : System} {ls : Files} (fs : List (FileName × Maybe FileContent)) -> All (λ (f₁ , v₁) → foldr extend sys ls f₁ ≡ v₁) fs -> Disjoint (map proj₁ fs) (map proj₁ ls) -> All (λ (f₁ , v₁) → sys f₁ ≡ v₁) fs
lemma2 [] all₁ dsj = All.[]
lemma2 {sys} {ls} ((f₁ , v₁) ∷ fs) (px All.∷ all₁) dsj = (trans (lemma3 f₁ ls λ x → dsj (here refl , x)) px) All.∷ (lemma2 fs all₁ λ x₁ → dsj (there (proj₁ x₁) , proj₂ x₁))

∈-resp-≡ : {ls ls₁ : List String} {v : String} -> v ∈ ls -> ls ≡ ls₁ -> v ∈ ls₁
∈-resp-≡ v∈ls ls≡ls₁ = subst (λ x → _ ∈ x) ls≡ls₁ v∈ls

runPreserves : {sys : System} (x x₁ : Cmd) -> (fs : List (FileName × Maybe FileContent)) -> Disjoint (cmdWriteNames x₁ sys) (cmdReadWrites x sys) -> IdempotentCmd cmdReadNames x fs sys -> IdempotentCmd cmdReadNames x fs (St.run x₁ sys)
runPreserves {sys} x x₁ fs dsj (IC .x .fs .sys x₂ ci) = IC x fs (St.run x₁ sys) ≡₁ λ all₁ f₁ → ≡₂ f₁ all₁
  where ≡₀ : proj₁ (oracle x) (St.run x₁ sys) ≡ proj₁ (oracle x) sys
        ≡₀ = sym (proj₂ (oracle x) sys (St.run x₁ sys) λ f₁ x₃ → lemma3 f₁ (proj₂ (proj₁ (oracle x₁) sys)) λ x₄ → dsj (x₄ , ∈-++⁺ˡ x₃))
        ≡₁ : map proj₁ fs ≡ cmdReadNames x (St.run x₁ sys)
        ≡₁ = trans x₂ (sym (cong (map proj₁ ∘ proj₁) ≡₀))
        ≡₂ : (f₁ : FileName) -> All (λ (f₁ , v₁) → St.run x₁ sys f₁ ≡ v₁) fs -> St.run x (St.run x₁ sys) f₁ ≡ St.run x₁ sys f₁
        ≡₂ f₁ all₁ with f₁ ∈? cmdWriteNames x (St.run x₁ sys)
        ... | no f₁∉ = sym (lemma3 f₁ (proj₂ (proj₁ (oracle x) (St.run x₁ sys))) f₁∉)
        ... | yes f₁∈ with f₁ ∈? cmdWriteNames x₁ sys
        ... | yes f₁∈₁ = contradiction (f₁∈₁ , ∈-++⁺ʳ _ (∈-resp-≡ f₁∈ (cong (map proj₁ ∘ proj₂) ≡₀))) dsj
        ... | no f₁∉ = trans (trans (lemma4 {St.run x₁ sys} {sys} (proj₂ (proj₁ (oracle x) (St.run x₁ sys))) f₁ f₁∈) (cong₂ (foldr extend sys ∘ proj₂) ≡₀ refl))
                             (trans (ci (lemma2 fs all₁ λ x₃ → dsj (proj₂ x₃ , ∈-++⁺ˡ (∈-resp-≡ (proj₁ x₃) x₂))) f₁) (lemma3 f₁ (proj₂ (proj₁ (oracle x₁) sys)) f₁∉))


preserves2 : {sys : System} {mm : Memory} (x : Cmd) -> IdempotentState cmdReadNames sys mm -> All (λ x₁ → Disjoint (cmdWriteNames x sys) (cmdReadWrites x₁ sys)) (map proj₁ mm) -> IdempotentState cmdReadNames (St.run x sys) mm
preserves2 x [] all₁ = []
preserves2 {sys} {(x₅ , _) ∷ mm} x (Cons ic is) (px All.∷ all₁) = Cons (runPreserves x₅ x _ px ic) (preserves2 x is all₁)


preserves : {sys : System} {mm : Memory} (x : Cmd) -> Disjoint (cmdReadNames x sys) (cmdWriteNames x sys) -> All (λ x₁ → Disjoint (cmdWriteNames x sys) (cmdReadWrites x₁ sys)) (map proj₁ mm) -> IdempotentState cmdReadNames sys mm -> IdempotentState cmdReadNames (St.run x sys) (save x (cmdReadNames x sys) (St.run x sys) mm)
preserves {sys} x dsj all₁ is = Cons ic (preserves2 x is all₁)
  where g₁ : (xs ys : List FileName) -> xs ≡ ys -> map proj₁ (map (λ f → f , St.run x sys f) xs) ≡ ys
        g₁ [] ys ≡₁ = ≡₁
        g₁ (x ∷ xs) (x₁ ∷ ys) ≡₁ with ∷-injective ≡₁
        ... | x≡x₁ , xs≡ys = cong₂ _∷_ x≡x₁ (g₁ xs ys xs≡ys)
        g₂ : cmdReadNames x sys ≡ cmdReadNames x (St.run x sys)
        g₂ with proj₂ (oracle x) sys (St.run x sys) (λ f₁ x₁ → (lemma3 f₁ (proj₂ (proj₁ (oracle x) sys)) λ x₂ → dsj (x₁ , x₂)))
        ... | ≡₁ = cong (map proj₁ ∘ proj₁) ≡₁
        ic : IdempotentCmd cmdReadNames x (map (λ f → f , St.run x sys f) (cmdReadNames x sys)) (St.run x sys)
        ic = IC x (map (λ f → f , St.run x sys f) (cmdReadNames x sys))
                  (St.run x sys)
                  (g₁ (cmdReadNames x sys) (cmdReadNames x (St.run x sys)) (g₂))
                  λ _ → cmdIdempotent sys x dsj

getCmdIdempotent : {f : (Cmd -> System -> List FileName)} {sys : System} (mm : Memory) (x : Cmd) -> IdempotentState f sys mm -> (x∈ : x ∈ map proj₁ mm) -> CmdIdempotent x (get x mm x∈) sys
getCmdIdempotent ((x₁ , fs) ∷ mm) x (Cons (IC .x₁ .fs _ ≡₂ x₃) is) x∈ with x ≟ x₁
... | yes x≡x₁ = subst (λ x₂ → CmdIdempotent x₂ _ _) (sym x≡x₁) x₃
... | no ¬x≡x₁ = getCmdIdempotent mm x is (tail ¬x≡x₁ x∈)


run≡ : (sys₁ sys₂ : System) (mm : Memory) (x : Cmd) -> (∀ f₁ → sys₁ f₁ ≡ sys₂ f₁) -> IdempotentState cmdReadNames sys₂ mm -> ∀ f₁ → St.run x sys₁ f₁ ≡ proj₁ (run (sys₂ , mm) x) f₁
run≡ sys₁ sys₂ mm x ∀₁ is f₁ with x ∈? map proj₁ mm
... | no x∉ = StP.lemma2 {sys₁} {sys₂} (proj₂ (oracle x) sys₁ sys₂ λ f₂ _ → ∀₁ f₂) (∀₁ f₁)
... | yes x∈ with maybeAll {sys₂} (get x mm x∈)
... | nothing = StP.lemma2 {sys₁} {sys₂} (proj₂ (oracle x) sys₁ sys₂ λ f₂ _ → ∀₁ f₂) (∀₁ f₁)
... | just all₁ with getCmdIdempotent mm x is x∈
... | ci = trans (StP.lemma2 {sys₁} {sys₂} (proj₂ (oracle x) sys₁ sys₂ λ f₂ _ → ∀₁ f₂) (∀₁ f₁))
                        (ci all₁ f₁)

helper : ∀ {s} ls ls₁ x → Disjoint (cmdWriteNames x s) ls₁ -> (concatMap (λ x₁ → cmdReadWriteNames x₁ s) ls) ⊆ ls₁ -> All (λ x₁ → Disjoint (cmdWriteNames x s) (cmdReadWriteNames x₁ s)) ls
helper [] ls₁ x dsj ⊆₁ = All.[]
helper {sys} (x₁ ∷ ls) ls₁ x dsj ⊆₁ = (λ x₂ → dsj ((proj₁ x₂) , ⊆₁ (∈-++⁺ˡ (proj₂ x₂)))) All.∷ (helper ls ls₁ x dsj λ x₂ → ⊆₁ (∈-++⁺ʳ (cmdReadWrites x₁ sys) x₂))


∃hazard : ∀ {v}{s}{x} ls {b} → v ∈ cmdWriteNames x s → v ∈ files ls → Hazard s x b ls
∃hazard ls v∈ws v∈files with ∈-++⁻ (filesRead ls) v∈files
... | inj₁ ∈₁ = ReadWrite _ _ _ _ v∈ws ∈₁
... | inj₂ ∈₂ = WriteWrite _ _ _ _ v∈ws ∈₂

helper3 : ∀ {s₁} {x₁} x → Disjoint (cmdWriteNames x₁ s₁) (cmdReadWriteNames x s₁) → cmdReadWrites x (St.run x₁ s₁) ≡ cmdReadWrites x s₁
helper3 {s₁} {x₁} x dsj = cong₂ _++_ ≡₁ ≡₂
  where ≡₀ : proj₁ (oracle x) (St.run x₁ s₁) ≡ proj₁ (oracle x) s₁
        ≡₀ = sym (proj₂ (oracle x) s₁ (St.run x₁ s₁) λ f₁ x₂ → (lemma3 f₁ (cmdWrites x₁ s₁) λ x₃ → dsj (x₃ , ∈-++⁺ˡ x₂)))
        ≡₁ : cmdReadNames x (St.run x₁ s₁) ≡ cmdReadNames x s₁
        ≡₁ = cong (map proj₁ ∘ proj₁) ≡₀
        ≡₂ : cmdWriteNames x (St.run x₁ s₁) ≡ cmdWriteNames x s₁
        ≡₂ = cong (map proj₁ ∘ proj₂) ≡₀

helper2 : ∀ {s₁} {x₂} ls → All (λ x₁ → Disjoint (cmdWriteNames x₂ s₁) (cmdReadWriteNames x₁ s₁)) ls → concatMap (λ x₁ → cmdReadWrites x₁ (St.run x₂ s₁)) ls ≡ concatMap (λ x₁ → cmdReadWrites x₁ s₁) ls
helper2 [] all₁ = refl
helper2 (x ∷ ls) (px All.∷ all₁) with helper2 ls all₁
... | a = cong₂ _++_ (helper3 x px) a

correct-inner : ∀ {s₁} {s₂} {ls} m b {b₁} → (∀ f₁ → s₁ f₁ ≡ s₂ f₁) → DisjointBuild s₁ b → Unique b → Unique (map proj₁ ls) → Disjoint b (map proj₁ ls) → concatMap (λ x₁ → cmdReadWrites x₁ s₁) (map proj₁ m) ⊆ files ls → IdempotentState cmdReadNames s₁ m → HazardFree s₁ b b₁ ls → (∀ f₁ → proj₁ (forward (s₁ , m) b) f₁ ≡ script s₂ b f₁)
correct-inner m [] ∀₁ _ _ _ _ _ is hf = ∀₁
correct-inner {s₁} {s₂} {ls} m (x ∷ b) ∀₁ (Cons x dc b dsb) (px ∷ ub) uls dsj ⊆₁ is (:: _ _ .x .b _ ¬hz hf) f₁ with x ∈? map proj₁ m
... | no x∉mem = correct-inner (save x (cmdReadNames x s₁) (St.run x s₁) m) b (run-≡ x ∀₁) dsb ub
                 (∉toAll _ (λ x₂ → dsj ((here refl) , x₂)) ∷ uls)
                 (λ x₂ → dsj ((there (proj₁ x₂)) , tail (λ x₃ → lookup px (proj₁ x₂) (sym x₃)) (proj₂ x₂)))
                 ⊆₂ is₂ hf f₁
  where all₁ : All (λ x₁ → Disjoint (cmdWriteNames x s₁) (cmdReadWriteNames x₁ s₁)) (map proj₁ m)
        all₁ = helper (map proj₁ m) _ x (λ x₂ → ¬hz (∃hazard _ (proj₁ x₂) (proj₂ x₂))) ⊆₁
        is₂ : IdempotentState cmdReadNames (St.run x s₁) (save x (cmdReadNames x s₁) (St.run x s₁) m)
        is₂ = preserves x dc all₁ is
        -- ( is
        ≡₀ : proj₁ (oracle x) (St.run x s₁) ≡ proj₁ (oracle x) s₁
        ≡₀ = sym (proj₂ (oracle x) s₁ (St.run x s₁) λ f₂ x₁ → lemma3 f₂ (cmdWrites x s₁) λ x₂ → dc (x₁ , x₂))
        ≡₁ : cmdReadNames x (St.run x s₁) ≡ cmdReadNames x s₁
        ≡₁ = cong (map proj₁ ∘ proj₁) ≡₀
        ≡₂ : cmdWriteNames x (St.run x s₁) ≡ cmdWriteNames x s₁
        ≡₂ = cong (map proj₁ ∘ proj₂) ≡₀
        ⊆₂ : concatMap (λ x₁ → cmdReadWrites x₁ (St.run x s₁)) (x ∷ map proj₁ m) ⊆ files (rec s₁ x ls)
        ⊆₂ x₂ with ∈-++⁻ (cmdReadWrites x (St.run x s₁)) x₂
        ... | inj₁ ∈₁ with ∈-++⁻ (cmdReadNames x (St.run x s₁)) ∈₁
        ... | inj₁ ∈rs = ∈-++⁺ˡ (∈-++⁺ˡ (subst (λ x₃ → _ ∈ x₃) ≡₁ ∈rs))
        ... | inj₂ ∈ws = ∈-++⁺ʳ (filesRead (rec s₁ x ls)) (∈-++⁺ˡ (subst (λ x₃ → _ ∈ x₃) ≡₂ ∈ws))
        ⊆₂ x₂ | inj₂ ∈₂ with ∈-++⁻ (filesRead ls) (⊆₁ (subst (λ x₃ → _ ∈ x₃) (helper2 (map proj₁ m) all₁) ∈₂))
        ... | inj₁ ∈₁ = ∈-++⁺ˡ (∈-++⁺ʳ (cmdReadNames x s₁) ∈₁)
        ... | inj₂ ∈₁ = ∈-++⁺ʳ (filesRead (rec s₁ x ls)) (∈-++⁺ʳ (cmdWriteNames x s₁) ∈₁)
... | yes x∈mem with maybeAll {s₁} (get x m x∈mem)
-- yes, it is extremely stupid that this is duplicated. i will fix it later
... | nothing = correct-inner (save x (cmdReadNames x s₁) (St.run x s₁) m) b (run-≡ x ∀₁) dsb ub
                 (∉toAll _ (λ x₂ → dsj ((here refl) , x₂)) ∷ uls)
                 (λ x₂ → dsj ((there (proj₁ x₂)) , tail (λ x₃ → lookup px (proj₁ x₂) (sym x₃)) (proj₂ x₂)))
                 ⊆₂ is₂ hf f₁
  where all₁ : All (λ x₁ → Disjoint (cmdWriteNames x s₁) (cmdReadWriteNames x₁ s₁)) (map proj₁ m)
        all₁ = helper (map proj₁ m) _ x (λ x₂ → ¬hz (∃hazard _ (proj₁ x₂) (proj₂ x₂))) ⊆₁
        is₂ : IdempotentState cmdReadNames (St.run x s₁) (save x (cmdReadNames x s₁) (St.run x s₁) m)
        is₂ = preserves x dc all₁ is
        -- ( is
        ≡₀ : proj₁ (oracle x) (St.run x s₁) ≡ proj₁ (oracle x) s₁
        ≡₀ = sym (proj₂ (oracle x) s₁ (St.run x s₁) λ f₂ x₁ → lemma3 f₂ (cmdWrites x s₁) λ x₂ → dc (x₁ , x₂))
        ≡₁ : cmdReadNames x (St.run x s₁) ≡ cmdReadNames x s₁
        ≡₁ = cong (map proj₁ ∘ proj₁) ≡₀
        ≡₂ : cmdWriteNames x (St.run x s₁) ≡ cmdWriteNames x s₁
        ≡₂ = cong (map proj₁ ∘ proj₂) ≡₀
        ⊆₂ : concatMap (λ x₁ → cmdReadWrites x₁ (St.run x s₁)) (x ∷ map proj₁ m) ⊆ files (rec s₁ x ls)
        ⊆₂ x₂ with ∈-++⁻ (cmdReadWrites x (St.run x s₁)) x₂
        ... | inj₁ ∈₁ with ∈-++⁻ (cmdReadNames x (St.run x s₁)) ∈₁
        ... | inj₁ ∈rs = ∈-++⁺ˡ (∈-++⁺ˡ (subst (λ x₃ → _ ∈ x₃) ≡₁ ∈rs))
        ... | inj₂ ∈ws = ∈-++⁺ʳ (filesRead (rec s₁ x ls)) (∈-++⁺ˡ (subst (λ x₃ → _ ∈ x₃) ≡₂ ∈ws))
        ⊆₂ x₂ | inj₂ ∈₂ with ∈-++⁻ (filesRead ls) (⊆₁ (subst (λ x₃ → _ ∈ x₃) (helper2 (map proj₁ m) all₁) ∈₂))
        ... | inj₁ ∈₁ = ∈-++⁺ˡ (∈-++⁺ʳ (cmdReadNames x s₁) ∈₁)
        ... | inj₂ ∈₁ = ∈-++⁺ʳ (filesRead (rec s₁ x ls)) (∈-++⁺ʳ (cmdWriteNames x s₁) ∈₁)
... | just all₁ with getCmdIdempotent m x is x∈mem
... | ci = correct-inner m b ∀₂ (dsj-≡ (St.run x s₁) s₁ b ∀₃ dsb) ub uls (λ x₂ → dsj (there (proj₁ x₂) , proj₂ x₂)) ⊆₁ is hf₂ f₁
  where ∀₃ : ∀ f₁ → s₁ f₁ ≡ St.run x s₁ f₁
        ∀₃ f₁ = (sym (ci all₁ f₁))
        ∀₂ : ∀ f₁ → s₁ f₁ ≡ St.run x s₂ f₁
        ∀₂ f₁ = trans (∀₃ f₁) (StP.lemma2 (proj₂ (oracle x) s₁ s₂ λ f₃ x₂ → ∀₁ f₃) (∀₁ f₁))
        hf₂ : HazardFree s₁ b _ _
        hf₂ = hf-still b [] ((x , cmdReadNames x s₁ , cmdWriteNames x s₁) ∷ []) _ (λ f₂ x₂ → sym (∀₃ f₂)) ub (∉toAll _ (λ x₂ → dsj ((here refl) , x₂)) ∷ uls) (λ x₂ → dsj (there (proj₁ x₂) , tail (λ x₃ → lookup px (proj₁ x₂) (sym x₃)) (proj₂ x₂))) hf
\end{code}

\begin{code}[hide]
correct : ∀ {s} b ls → DisjointBuild s b → Unique b → Unique (map proj₁ ls) → Disjoint b (map proj₁ ls) → HazardFree s b b ls → (∀ f₁ → proj₁ (forward (s , _) b) f₁ ≡ script s b f₁)
correct b ls dsb ub uls dsj hf = correct-inner [] b (λ f₁ → refl) dsb ub uls dsj (λ ()) [] hf
\end{code}

\newcommand{\correctF}{%
\begin{code}
forward_correct : ∀ {s} b → HazardFree s b b [] → (∀ f₁ → proj₁ (forward (s , []) b) f₁ ≡ script s b f₁)
\end{code}}
\begin{code}[hide]
forward_correct b hf = correct b [] {!!} {!!} Data.List.Relation.Unary.AllPairs.[] g₁ hf
  where g₁ : Disjoint b []
        g₁ ()
\end{code}

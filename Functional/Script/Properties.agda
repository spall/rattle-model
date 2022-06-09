
open import Functional.State using (Oracle ; FileSystem ; Cmd ; extend)

module Functional.Script.Properties (oracle : Oracle) where

open import Functional.Script.Hazard (oracle) using (HazardFree ; _∷_)
open import Functional.Script.Hazard.Properties (oracle) using  (hf=>disjoint0)
open import Agda.Builtin.Equality
open import Functional.State.Helpers (oracle) using (run ; cmdWriteNames ; cmdReadNames)
open import Functional.State.Properties (oracle) as St
open import Data.Empty using (⊥)
open import Functional.Build (oracle) using (Build ; DisjointBuild ; Cons ; Null)
open import Functional.Script.Exec (oracle) as S using (script ; buildReadNames ; h₄ ; buildWriteNames)
open import Data.List using (List ; _∷ʳ_ ; _∷_ ; _++_ ; [] ; reverse ; map ; foldr)
open import Data.List.Properties using (++-identityʳ ; ++-assoc) 
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (subst ; sym ; decSetoid ; trans ; cong ; cong₂ ; cong-app)
open import Common.List.Properties as CLP using (∈→before-∷ʳ)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.Product using (proj₂ ; proj₁ ; _,_ ; ∃-syntax ; _×_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.String.Properties using (_≟_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈?_ ; _∉_ ; _∈_)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Data.List.Relation.Unary.All.Properties using (++⁻ ; ++⁻ˡ)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ ; ∈-++⁺ˡ ; ∈-++⁻ ; ∈-insert)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Function using (_∘_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_ ; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Nullary using (yes ; no)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
--- ---

h₅ : (s s₁ : FileSystem) (x : Cmd) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (cmdReadNames x s₁) -> proj₁ (oracle x) s ≡ proj₁ (oracle x) s₁
h₅ s s₁ x all₁ = sym (proj₂ (oracle x) s₁ s λ f₁ x₁ → sym (lookup all₁ x₁))

--- exec properties ---

exec-∷ʳ : (s : FileSystem) (x : Cmd) (b : Build) -> run x (script b s) ≡ script (b ∷ʳ x) s
exec-∷ʳ s x [] = refl
exec-∷ʳ s x (x₁ ∷ b) = exec-∷ʳ (run x₁ s) x b


exec-∷≡ : (f₁ : String) (s s₁ : FileSystem) (b : Build) -> All (λ f₂ → s f₂ ≡ s₁ f₂) (buildReadNames s₁ b) -> s f₁ ≡ s₁ f₁ -> script b s f₁ ≡ script b s₁ f₁
exec-∷≡ f₁ s s₁ [] all₁ ≡₁ = ≡₁
exec-∷≡ f₁ s s₁ (x₁ ∷ b) all₁ ≡₁ with ++⁻ (cmdReadNames x₁ s₁) all₁ 
... | all₂ , all₃ = exec-∷≡ f₁ (run x₁ s) (run x₁ s₁) b (St.lemma1-sym {s} {s₁} (buildReadNames (run x₁ s₁) b) x₁ all₂ all₃)
                            (St.lemma2 {s} {s₁} (h₄ s s₁ x₁ all₂) ≡₁)


-- this is a copy of lemma9 so just replace lemma9 with this
exec-≡sys : (s : FileSystem) (f₁ : String) (xs : Build) -> f₁ ∉ buildWriteNames s xs -> script xs s f₁ ≡ s f₁
exec-≡sys s f₁ [] f₁∉ = refl
exec-≡sys s f₁ (x ∷ xs) f₁∉ = trans (exec-≡sys (run x s) f₁ xs (λ x₁ → f₁∉ (∈-++⁺ʳ (cmdWriteNames x s) x₁)))
                                    (sym (St.lemma3 {s} f₁ (proj₂ (proj₁ (oracle x) s)) λ x₁ → f₁∉ (∈-++⁺ˡ x₁)))

{- if f₁ is not in the writes if ys then f₁ is the same in the system before and after ys executes -}

exec-≡f₁ : (s : FileSystem) (f₁ : String) (xs ys : Build) -> f₁ ∉ buildWriteNames (script xs s) ys -> script xs s f₁ ≡ script (xs ++ ys) s f₁
exec-≡f₁ s f₁ [] ys f₁∉ = sym (exec-≡sys s f₁ ys f₁∉)
exec-≡f₁ s f₁ (x ∷ xs) ys f₁∉ = exec-≡f₁ (run x s) f₁ xs ys f₁∉

exec≡₃ : {sys : FileSystem} (x : Cmd) (xs : Build) -> run x (script xs sys) ≡ script (xs ∷ʳ x) sys
exec≡₃ x [] = refl
exec≡₃ {s} x (x₁ ∷ xs) = exec≡₃ {run x₁ s} x xs

exec≡₄ : {sys : FileSystem} (xs ys : Build) -> script (xs ++ ys) sys ≡ script ys (script xs sys)
exec≡₄ [] ys = refl
exec≡₄ {sys} (x ∷ xs) ys = exec≡₄ {run x sys} xs ys

exec≡₅ : {sys : FileSystem} (x : Cmd) (xs ys : Build) -> script ys (run x (script xs sys)) ≡ script (xs ++ x ∷ ys) sys
exec≡₅ x [] ys = refl
exec≡₅ {sys} x (x₁ ∷ xs) ys = exec≡₅ {run x₁ sys} x xs ys

all≡ : (s : FileSystem) (fs : List String) (xs ys zs : Build) -> Disjoint fs (buildWriteNames (script ys s) zs) -> (∀ f₁ → script xs s f₁ ≡ script (ys ++ zs) s f₁) -> All (λ f₁ → script xs s f₁ ≡ script ys s f₁) fs
all≡ s [] xs ys zs dsj ∀₁ = All.[]
all≡ s (x ∷ fs) xs ys zs dsj ∀₁ = trans (∀₁ x) (sym (exec-≡f₁ s x ys zs λ x₁ → dsj (here refl , x₁))) All.∷ (all≡ s fs xs ys zs (λ x₁ → dsj (there (proj₁ x₁) , proj₂ x₁)) ∀₁)


writes≡ : (s s₁ : FileSystem) (ys : Build) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (buildReadNames s₁ ys) -> buildWriteNames s ys ≡ buildWriteNames s₁ ys
writes≡ s s₁ [] all₁ = refl
writes≡ s s₁ (x₁ ∷ ys) all₁ with ++⁻ (cmdReadNames x₁ s₁) all₁
... | all₂ , all₃ = cong₂ _++_ (cong ((map proj₁) ∘ proj₂) (h₅ s s₁ x₁ all₂))
                                    (writes≡ (run x₁ s) (run x₁ s₁) ys (St.lemma1-sym {s} {s₁} (buildReadNames (run x₁ s₁) ys) x₁ all₂ all₃))
                                    
exec-f₁≡ : ∀ s f₁ x xs ys zs -> (∀ f₂ → script xs s f₂ ≡ script (ys ++ zs) s f₂) -> proj₁ (oracle x) (script xs s) ≡ proj₁ (oracle x) (script ys s) -> All (λ f₂ → script ys s f₂ ≡ run x (script ys s) f₂) (buildReadNames (run x (script ys s)) zs) -> Disjoint (cmdWriteNames x (script ys s)) (buildWriteNames (run x (script ys s)) zs) -> script (xs ∷ʳ x) s f₁ ≡ script (ys ++ x ∷ zs) s f₁
exec-f₁≡ s f₁ x xs ys zs ∀₁ ≡₀ all₁ dsj with f₁ ∈? cmdWriteNames x (script xs s)
... | yes f₁∈ with exec-≡sys (run x (script ys s)) f₁ zs f₁∉
  where f₁∉ : f₁ ∉ buildWriteNames (run x (script ys s)) zs
        f₁∉ = λ x₁ → dsj (subst (λ x₂ → f₁ ∈ map proj₁ (proj₂ x₂)) ≡₀ f₁∈ , x₁)
... | a = trans ≡₁ (trans (sym a) (cong-app (exec≡₅ {s} x ys zs) f₁))
  where ≡₁ : script (xs ∷ʳ x) s f₁ ≡ run x (script ys s) f₁
        ≡₁ with (cong proj₂ ≡₀)
        ... | a₁ with St.lemma4 {script xs s} {script ys s} (proj₂ (proj₁ (oracle x) (script xs s))) f₁ f₁∈
        ... | a₂ = trans (cong-app (sym (exec≡₃ {s} x xs)) f₁) (subst (λ x₁ → foldr extend (script xs s) (proj₂ (proj₁ (oracle x) (script xs s))) f₁ ≡ foldr extend (script ys s) (proj₂ x₁) f₁) ≡₀ a₂)
-- prove exec s (xs ∷ʳ x) f₁ ≡ run oracle x (exec s ys) f₁ ≡ exec s (ys ++ x ∷ zs) f₁
exec-f₁≡ s f₁ x xs ys zs ∀₁ ≡₀ all₁ dsj | no f₁∉  = trans ≡₁ (trans (∀₁ f₁) ≡₂)
  where ≡₁ : script (xs ∷ʳ x) s f₁ ≡ script xs s f₁
        ≡₁ = sym (trans (St.lemma3 {script xs s} f₁ (proj₂ (proj₁ (oracle x) (script xs s))) f₁∉)
                        (cong-app (exec-∷ʳ s x xs) f₁))
        f₁∉₁ : f₁ ∉ cmdWriteNames x (script ys s)
        f₁∉₁ = subst (λ x₁ → f₁ ∉ map proj₁ (proj₂ x₁)) ≡₀ f₁∉
        ≡₂ : script (ys ++ zs) s f₁ ≡ script (ys ++ x ∷ zs) s f₁
        ≡₂ with exec-∷≡ f₁ (script ys s) (run x (script ys s)) zs all₁ (St.lemma3 {script ys s} f₁ (proj₂ (proj₁ (oracle x) (script ys s))) f₁∉₁)
        ... | a = trans (cong-app (exec≡₄ {s} ys zs) f₁) (trans a (cong-app (exec≡₅ {s} x ys zs) f₁))
-- prove exec s (xs ∷ x) f₁ ≡ exec s xs f₁ ≡ exec s (ys ++ zs) f₁ ≡ exec s (xs ++ x ∷ ys) f₁

dsj-≡ : ∀ s₁ s₂ b₁ → (∀ f₁ → s₂ f₁ ≡ s₁ f₁) → DisjointBuild s₁ b₁ → DisjointBuild s₂ b₁
dsj-≡ s₁ s₂ .[] ∀₁ Null = Null
dsj-≡ s₁ s₂ .(x ∷ b) ∀₁ (Cons x dsj b dsb) = Cons x (λ x₂ → dsj (v∈reads (proj₁ x₂) , v∈writes (proj₂ x₂))) b (dsj-≡ (run x s₁) (run x s₂) b (St.run-≡ x ∀₁) dsb)
  where ≡₁ : proj₁ (oracle x) s₂ ≡ proj₁ (oracle x) s₁
        ≡₁ = proj₂ (oracle x) s₂ s₁ λ f₁ x₁ → ∀₁ f₁
        v∈reads : ∀ {v} → v ∈ cmdReadNames x s₂ → v ∈ cmdReadNames x s₁
        v∈reads v∈ = subst (λ x₁ → _ ∈ x₁) (cong (map proj₁ ∘ proj₁) ≡₁) v∈
        v∈writes : ∀ {v} → v ∈ cmdWriteNames x s₂ → v ∈ cmdWriteNames x s₁
        v∈writes v∈ = subst (λ x₁ → _ ∈ x₁) (cong (map proj₁ ∘ proj₂) ≡₁) v∈


still-disjoint : ∀ {b₁} {ls} s₁ s₂ b → HazardFree s₁ b b₁ ls → (∀ f₁ → f₁ ∉ buildWriteNames s₁ b → s₁ f₁ ≡ s₂ f₁) → DisjointBuild s₁ b → DisjointBuild s₂ b
still-disjoint s₁ s₂ [] hf ∀₁ dsj = Null
still-disjoint s₁ s₂ (x ∷ b) (¬hz ∷ hf) ∀₁ (Cons .x dsj .b dsb)
    = Cons x g₀ b (still-disjoint (run x s₁) (run x s₂) b hf (λ f₁ x₃ → g₁ f₁ x₃) dsb)
      where g₂ : ∀ f₁ → f₁ ∉ cmdWriteNames x s₁ → f₁ ∉ buildWriteNames (run x s₁) b → f₁ ∈ buildWriteNames s₁ (x ∷ b) → ⊥
            g₂ f₁ f₁∉₁ f₁∉₂ f₁∈ with ∈-++⁻ (cmdWriteNames x s₁) f₁∈
            ... | inj₁ ∈₁ = contradiction ∈₁ f₁∉₁
            ... | inj₂ ∈₂ = contradiction ∈₂ f₁∉₂
            -- this is a common pattern.... would be nice to have had this somewhere to reuse.
            g₃ : ∀ f₁ → f₁ ∈ cmdReadNames x s₁ → s₁ f₁ ≡ s₂ f₁
            g₃ f₁ f₁∈ with hf=>disjoint0 s₁ x b _ (¬hz ∷ hf)
            ... | dsj₂ = ∀₁ f₁ λ x₁ → g₂ f₁ (λ x₂ → dsj (f₁∈ , x₂))
                          (λ x₂ → dsj₂ (f₁∈ , x₂)) x₁
        
            g₁ : ∀ f₁ → f₁ ∉ buildWriteNames (run x s₁) b → run x s₁ f₁ ≡ run x s₂ f₁
            g₁ f₁ f₁∉ with proj₂ (oracle x) s₁ s₂ (λ f₂ x₁ → g₃ f₂ x₁)
            ... | ≡₁ with f₁ ∈? cmdWriteNames x s₁
            ... | yes f₁∈ws = subst (λ x₁ → foldr extend s₁ (proj₂ (proj₁ (oracle x) s₁)) f₁ ≡ foldr extend s₂ x₁ f₁)
                                    (cong proj₂ ≡₁)
                                    (lemma4 {s₁} {s₂} (proj₂ (proj₁ (oracle x) s₁)) f₁ f₁∈ws) 
            ... | no f₁∉ws = lemma2 ≡₁ (∀₁ f₁ λ x₁ → g₂ f₁ f₁∉ws f₁∉ x₁)
            g₀ : Disjoint (cmdReadNames x s₂) (cmdWriteNames x s₂)
            g₀ x₁ with proj₂ (oracle x) s₁ s₂ (λ f₂ x₁ → g₃ f₂ x₁)
            ... | ≡₁ = dsj (subst (λ x₂ → _ ∈ x₂) (cong (map proj₁ ∘ proj₁) (sym ≡₁)) (proj₁ x₁)
                          , subst (λ x₂ → _ ∈ x₂) (cong (map proj₁ ∘ proj₂) (sym ≡₁)) (proj₂ x₁))

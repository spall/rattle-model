
open import Functional.State as St using (F ; System ; Cmd ; run ; trace)

module Functional.Script.Properties (oracle : F) where

open import Agda.Builtin.Equality
open import Data.Empty using (⊥)
open import Functional.Build using (Build)
open import Functional.Script.Exec (oracle) as S
open import Data.List using (List ; _∷ʳ_ ; _∷_ ; _++_ ; [] ; reverse ; map ; foldr)
open import Data.List.Properties using (++-identityʳ ; ++-assoc) 
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (subst ; sym ; decSetoid ; trans ; cong ; cong₂ ; cong-app)
open import Common.List.Properties as CLP using (_before_en_ ; ∈→before-∷ʳ)
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
--- ---

h₅ : (s s₁ : System) (x : Cmd) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (Creads s₁ x) -> proj₁ (oracle x) s ≡ proj₁ (oracle x) s₁
h₅ s s₁ x all₁ = sym (proj₂ (oracle x) s₁ s λ f₁ x₁ → sym (lookup all₁ x₁))


--- exec properties ---

exec-∷ʳ : (s : System) (x : Cmd) (b : Build) -> run oracle x (S.exec s b) ≡ S.exec s (b ∷ʳ x)
exec-∷ʳ s x [] = refl
exec-∷ʳ s x (x₁ ∷ b) = exec-∷ʳ (run oracle x₁ s) x b

exec-∷≡ : (f₁ : String) (s s₁ : System) (b : Build) -> All (λ f₂ → s f₂ ≡ s₁ f₂) (reads s₁ b) -> s f₁ ≡ s₁ f₁ -> exec s b f₁ ≡ exec s₁ b f₁
exec-∷≡ f₁ s s₁ [] all₁ ≡₁ = ≡₁
exec-∷≡ f₁ s s₁ (x₁ ∷ b) all₁ ≡₁ with ++⁻ (Creads s₁ x₁) all₁ 
... | all₂ , all₃ = exec-∷≡ f₁ (run oracle x₁ s) (run oracle x₁ s₁) b (St.lemma1-sym {oracle} {s} {s₁} (reads (run oracle x₁ s₁) b) x₁ all₂ all₃)
                            (St.lemma2 {oracle} {s} {s₁} x₁ f₁ (h₄ s s₁ x₁ all₂) ≡₁)


-- this is a copy of lemma9 so just replace lemma9 with this
exec-≡sys : (s : System) (f₁ : String) (xs : Build) -> f₁ ∉ writes s xs -> exec s xs f₁ ≡ s f₁
exec-≡sys s f₁ [] f₁∉ = refl
exec-≡sys s f₁ (x ∷ xs) f₁∉ = trans (exec-≡sys (run oracle x s) f₁ xs (λ x₁ → f₁∉ (∈-++⁺ʳ (Cwrites s x) x₁)))
                                    (sym (St.lemma3 {s} f₁ (proj₂ (proj₁ (oracle x) s)) λ x₁ → f₁∉ (∈-++⁺ˡ x₁)))

{- if f₁ is not in the writes if ys then f₁ is the same in the system before and after ys executes -}
exec-≡f₁ : (s : System) (f₁ : String) (xs ys : Build) -> f₁ ∉ writes (exec s xs) ys -> exec s xs f₁ ≡ exec s (xs ++ ys) f₁
exec-≡f₁ s f₁ [] ys f₁∉ = sym (exec-≡sys s f₁ ys f₁∉)
exec-≡f₁ s f₁ (x ∷ xs) ys f₁∉ = exec-≡f₁ (run oracle x s) f₁ xs ys f₁∉

exec≡₃ : {sys : System} (x : Cmd) (xs : Build) -> run oracle x (exec sys xs) ≡ exec sys (xs ∷ʳ x)
exec≡₃ x [] = refl
exec≡₃ {s} x (x₁ ∷ xs) = exec≡₃ {run oracle x₁ s} x xs

exec≡₄ : {sys : System} (xs ys : Build) -> exec sys (xs ++ ys) ≡ exec (exec sys xs) ys
exec≡₄ [] ys = refl
exec≡₄ {sys} (x ∷ xs) ys = exec≡₄ {run oracle x sys} xs ys

exec≡₅ : {sys : System} (x : Cmd) (xs ys : Build) -> exec (run oracle x (exec sys xs)) ys ≡ exec sys (xs ++ x ∷ ys)
exec≡₅ x [] ys = refl
exec≡₅ {sys} x (x₁ ∷ xs) ys = exec≡₅ {run oracle x₁ sys} x xs ys

-- build-rws --

-- i think i can just use foldr-∷ʳ if i redefine the function using foldr
build-rws-∷ʳ : (s : System) (ls : List String) (x : Cmd) (b : Build) -> S.read-writes (S.exec s b) x ++ S.build-rws s b ls ≡ S.build-rws s (b ∷ʳ x) ls
build-rws-∷ʳ s ls x [] = refl
build-rws-∷ʳ s ls x (x₁ ∷ b) = build-rws-∷ʳ (run oracle x₁ s) (S.read-writes s x₁ ++ ls) x b

all≡ : (s : System) (fs : List String) (xs ys zs : Build) -> Disjoint fs (writes (exec s ys) zs) -> (∀ f₁ → exec s xs f₁ ≡ exec s (ys ++ zs) f₁) -> All (λ f₁ → exec s xs f₁ ≡ exec s ys f₁) fs
all≡ s [] xs ys zs dsj ∀₁ = All.[]
all≡ s (x ∷ fs) xs ys zs dsj ∀₁ = trans (∀₁ x) (sym (exec-≡f₁ s x ys zs λ x₁ → dsj (here refl , x₁))) All.∷ (all≡ s fs xs ys zs (λ x₁ → dsj (there (proj₁ x₁) , proj₂ x₁)) ∀₁)

writes≡ : (s s₁ : System) (ys : Build) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (reads s₁ ys) -> writes s ys ≡ writes s₁ ys
writes≡ s s₁ [] all₁ = refl
writes≡ s s₁ (x₁ ∷ ys) all₁ with ++⁻ (Creads s₁ x₁) all₁
... | all₂ , all₃ = cong₂ _++_ (cong ((map proj₁) ∘ proj₂) (h₅ s s₁ x₁ all₂))
                                    (writes≡ (run oracle x₁ s) (run oracle x₁ s₁) ys (St.lemma1-sym {oracle} {s} {s₁} (reads (run oracle x₁ s₁) ys) x₁ all₂ all₃))

-- basically a wrapper around subst but nice for writing lemmas because it keeps code less confusing
still-disjoint : (s : System) (x : Cmd) (ys : Build) -> Disjoint (Cwrites s x) (reads (run oracle x s) ys) -> Disjoint (Creads s x) (writes (run oracle x s) ys) -> Disjoint (Creads s x) (writes s ys)
still-disjoint s x ys dsj₁ dsj₂ = subst (λ x₁ → Disjoint _ x₁) (sym (writes≡ s (run oracle x s) ys (St.lemma5 {s} (reads (run oracle x s) ys) (proj₂ (proj₁ (oracle x) s)) dsj₁))) dsj₂


exec-f₁≡ : (s : System) (f₁ : String) (x : Cmd) (xs ys zs : Build) -> (∀ f₂ → exec s xs f₂ ≡ exec s (ys ++ zs) f₂) -> proj₁ (oracle x) (exec s xs) ≡ proj₁ (oracle x) (exec s ys) -> All (λ f₂ → exec s ys f₂ ≡ run oracle x (exec s ys) f₂) (reads (run oracle x (exec s ys)) zs) -> Disjoint (Cwrites (exec s ys) x) (writes (run oracle x (exec s ys)) zs) -> exec s (xs ∷ʳ x) f₁ ≡ exec s (ys ++ x ∷ zs) f₁
exec-f₁≡ s f₁ x xs ys zs ∀₁ ≡₀ all₁ dsj with f₁ ∈? Cwrites (exec s xs) x
... | yes f₁∈ with exec-≡sys (run oracle x (exec s ys)) f₁ zs f₁∉
  where f₁∉ : f₁ ∉ writes (run oracle x (exec s ys)) zs
        f₁∉ = λ x₁ → dsj (subst (λ x₂ → f₁ ∈ map proj₁ (proj₂ x₂)) ≡₀ f₁∈ , x₁)
... | a = trans ≡₁ (trans (sym a) (cong-app (exec≡₅ {s} x ys zs) f₁))
  where ≡₁ : exec s (xs ∷ʳ x) f₁ ≡ run oracle x (exec s ys) f₁
        ≡₁ with (cong proj₂ ≡₀)
        ... | a₁ with St.lemma4 {exec s xs} {exec s ys} (proj₂ (proj₁ (oracle x) (exec s xs))) f₁ f₁∈
        ... | a₂ = trans (cong-app (sym (exec≡₃ {s} x xs)) f₁) (subst (λ x₁ → foldr St.extend (exec s xs) (proj₂ (proj₁ (oracle x) (exec s xs))) f₁ ≡ foldr St.extend (exec s ys) (proj₂ x₁) f₁) ≡₀ a₂)
-- prove exec s (xs ∷ʳ x) f₁ ≡ run oracle x (exec s ys) f₁ ≡ exec s (ys ++ x ∷ zs) f₁
exec-f₁≡ s f₁ x xs ys zs ∀₁ ≡₀ all₁ dsj | no f₁∉  = trans ≡₁ (trans (∀₁ f₁) ≡₂)
  where ≡₁ : exec s (xs ∷ʳ x) f₁ ≡ exec s xs f₁
        ≡₁ = sym (trans (St.lemma3 {exec s xs} f₁ (proj₂ (proj₁ (oracle x) (exec s xs))) f₁∉)
                        (cong-app (exec-∷ʳ s x xs) f₁))
        f₁∉₁ : f₁ ∉ Cwrites (exec s ys) x
        f₁∉₁ = subst (λ x₁ → f₁ ∉ map proj₁ (proj₂ x₁)) ≡₀ f₁∉
        ≡₂ : exec s (ys ++ zs) f₁ ≡ exec s (ys ++ x ∷ zs) f₁
        ≡₂ with exec-∷≡ f₁ (exec s ys) (run oracle x (exec s ys)) zs all₁ (St.lemma3 {exec s ys} f₁ (proj₂ (proj₁ (oracle x) (exec s ys))) f₁∉₁)
        ... | a = trans (cong-app (exec≡₄ {s} ys zs) f₁) (trans a (cong-app (exec≡₅ {s} x ys zs) f₁))
-- prove exec s (xs ∷ x) f₁ ≡ exec s xs f₁ ≡ exec s (ys ++ zs) f₁ ≡ exec s (xs ++ x ∷ ys) f₁

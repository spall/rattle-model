
open import Functional.State using (Oracle ; System ; Cmd ; extend)

module Functional.Script.Properties (oracle : Oracle) where

-- open import Functional.Script.HazardFree (oracle) using (HazardFree)
open import Agda.Builtin.Equality
open import Functional.State.Helpers (oracle) using (run ; cmdWriteNames ; cmdReadNames)
open import Functional.State.Properties (oracle) as St
open import Data.Empty using (⊥)
open import Functional.Build using (Build)
open import Functional.Script.Exec (oracle) as S renaming (script to exec)
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
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
--- ---

h₅ : (s s₁ : System) (x : Cmd) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (cmdReadNames x s₁) -> proj₁ (oracle x) s ≡ proj₁ (oracle x) s₁
h₅ s s₁ x all₁ = sym (proj₂ (oracle x) s₁ s λ f₁ x₁ → sym (lookup all₁ x₁))

--- exec properties ---

exec-∷ʳ : (s : System) (x : Cmd) (b : Build) -> run x (exec s b) ≡ exec s (b ∷ʳ x)
exec-∷ʳ s x [] = refl
exec-∷ʳ s x (x₁ ∷ b) = exec-∷ʳ (run x₁ s) x b


exec-∷≡ : (f₁ : String) (s s₁ : System) (b : Build) -> All (λ f₂ → s f₂ ≡ s₁ f₂) (buildReadNames s₁ b) -> s f₁ ≡ s₁ f₁ -> exec s b f₁ ≡ exec s₁ b f₁
exec-∷≡ f₁ s s₁ [] all₁ ≡₁ = ≡₁
exec-∷≡ f₁ s s₁ (x₁ ∷ b) all₁ ≡₁ with ++⁻ (cmdReadNames x₁ s₁) all₁ 
... | all₂ , all₃ = exec-∷≡ f₁ (run x₁ s) (run x₁ s₁) b (St.lemma1-sym {s} {s₁} (buildReadNames (run x₁ s₁) b) x₁ all₂ all₃)
                            (St.lemma2 {s} {s₁} (h₄ s s₁ x₁ all₂) ≡₁)


-- this is a copy of lemma9 so just replace lemma9 with this
exec-≡sys : (s : System) (f₁ : String) (xs : Build) -> f₁ ∉ buildWriteNames s xs -> exec s xs f₁ ≡ s f₁
exec-≡sys s f₁ [] f₁∉ = refl
exec-≡sys s f₁ (x ∷ xs) f₁∉ = trans (exec-≡sys (run x s) f₁ xs (λ x₁ → f₁∉ (∈-++⁺ʳ (cmdWriteNames x s) x₁)))
                                    (sym (St.lemma3 {s} f₁ (proj₂ (proj₁ (oracle x) s)) λ x₁ → f₁∉ (∈-++⁺ˡ x₁)))

{- if f₁ is not in the writes if ys then f₁ is the same in the system before and after ys executes -}

exec-≡f₁ : (s : System) (f₁ : String) (xs ys : Build) -> f₁ ∉ buildWriteNames (exec s xs) ys -> exec s xs f₁ ≡ exec s (xs ++ ys) f₁
exec-≡f₁ s f₁ [] ys f₁∉ = sym (exec-≡sys s f₁ ys f₁∉)
exec-≡f₁ s f₁ (x ∷ xs) ys f₁∉ = exec-≡f₁ (run x s) f₁ xs ys f₁∉

exec≡₃ : {sys : System} (x : Cmd) (xs : Build) -> run x (exec sys xs) ≡ exec sys (xs ∷ʳ x)
exec≡₃ x [] = refl
exec≡₃ {s} x (x₁ ∷ xs) = exec≡₃ {run x₁ s} x xs

exec≡₄ : {sys : System} (xs ys : Build) -> exec sys (xs ++ ys) ≡ exec (exec sys xs) ys
exec≡₄ [] ys = refl
exec≡₄ {sys} (x ∷ xs) ys = exec≡₄ {run x sys} xs ys

exec≡₅ : {sys : System} (x : Cmd) (xs ys : Build) -> exec (run x (exec sys xs)) ys ≡ exec sys (xs ++ x ∷ ys)
exec≡₅ x [] ys = refl
exec≡₅ {sys} x (x₁ ∷ xs) ys = exec≡₅ {run x₁ sys} x xs ys

-- build-rws --

-- i think i can just use foldr-∷ʳ if i redefine the function using foldr
{-
build-rws-∷ʳ : (s : System) (ls : List String) (x : Cmd) (b : Build) -> S.read-writes (S.exec s b) x ++ S.build-rws s b ls ≡ S.build-rws s (b ∷ʳ x) ls
build-rws-∷ʳ s ls x [] = refl
build-rws-∷ʳ s ls x (x₁ ∷ b) = build-rws-∷ʳ (run oracle x₁ s) (S.read-writes s x₁ ++ ls) x b
-}

all≡ : (s : System) (fs : List String) (xs ys zs : Build) -> Disjoint fs (buildWriteNames (exec s ys) zs) -> (∀ f₁ → exec s xs f₁ ≡ exec s (ys ++ zs) f₁) -> All (λ f₁ → exec s xs f₁ ≡ exec s ys f₁) fs
all≡ s [] xs ys zs dsj ∀₁ = All.[]
all≡ s (x ∷ fs) xs ys zs dsj ∀₁ = trans (∀₁ x) (sym (exec-≡f₁ s x ys zs λ x₁ → dsj (here refl , x₁))) All.∷ (all≡ s fs xs ys zs (λ x₁ → dsj (there (proj₁ x₁) , proj₂ x₁)) ∀₁)


writes≡ : (s s₁ : System) (ys : Build) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (buildReadNames s₁ ys) -> buildWriteNames s ys ≡ buildWriteNames s₁ ys
writes≡ s s₁ [] all₁ = refl
writes≡ s s₁ (x₁ ∷ ys) all₁ with ++⁻ (cmdReadNames x₁ s₁) all₁
... | all₂ , all₃ = cong₂ _++_ (cong ((map proj₁) ∘ proj₂) (h₅ s s₁ x₁ all₂))
                                    (writes≡ (run x₁ s) (run x₁ s₁) ys (St.lemma1-sym {s} {s₁} (buildReadNames (run x₁ s₁) ys) x₁ all₂ all₃))
                                    
{-
-- basically a wrapper around subst but nice for writing lemmas because it keeps code less confusing
still-disjoint : (s : System) (x : Cmd) (ys : Build) -> Disjoint (cmdWriteNames x s) (buildReadNames (run oracle x s) ys) -> Disjoint (cmdReadNames x s) (buildWriteNames (run oracle x s) ys) -> Disjoint (cmdReadNames x s) (buildWriteNames s ys)
still-disjoint s x ys dsj₁ dsj₂ = subst (λ x₁ → Disjoint _ x₁) (sym (writes≡ s (run oracle x s) ys (St.lemma5 {s} (reads (run oracle x s) ys) (proj₂ (proj₁ (oracle x) s)) dsj₁))) dsj₂
-}

exec-f₁≡ : ∀ s f₁ x xs ys zs -> (∀ f₂ → exec s xs f₂ ≡ exec s (ys ++ zs) f₂) -> proj₁ (oracle x) (exec s xs) ≡ proj₁ (oracle x) (exec s ys) -> All (λ f₂ → exec s ys f₂ ≡ run x (exec s ys) f₂) (buildReadNames (run x (exec s ys)) zs) -> Disjoint (cmdWriteNames x (exec s ys)) (buildWriteNames (run x (exec s ys)) zs) -> exec s (xs ∷ʳ x) f₁ ≡ exec s (ys ++ x ∷ zs) f₁
exec-f₁≡ s f₁ x xs ys zs ∀₁ ≡₀ all₁ dsj with f₁ ∈? cmdWriteNames x (exec s xs)
... | yes f₁∈ with exec-≡sys (run x (exec s ys)) f₁ zs f₁∉
  where f₁∉ : f₁ ∉ buildWriteNames (run x (exec s ys)) zs
        f₁∉ = λ x₁ → dsj (subst (λ x₂ → f₁ ∈ map proj₁ (proj₂ x₂)) ≡₀ f₁∈ , x₁)
... | a = trans ≡₁ (trans (sym a) (cong-app (exec≡₅ {s} x ys zs) f₁))
  where ≡₁ : exec s (xs ∷ʳ x) f₁ ≡ run x (exec s ys) f₁
        ≡₁ with (cong proj₂ ≡₀)
        ... | a₁ with St.lemma4 {exec s xs} {exec s ys} (proj₂ (proj₁ (oracle x) (exec s xs))) f₁ f₁∈
        ... | a₂ = trans (cong-app (sym (exec≡₃ {s} x xs)) f₁) (subst (λ x₁ → foldr extend (exec s xs) (proj₂ (proj₁ (oracle x) (exec s xs))) f₁ ≡ foldr extend (exec s ys) (proj₂ x₁) f₁) ≡₀ a₂)
-- prove exec s (xs ∷ʳ x) f₁ ≡ run oracle x (exec s ys) f₁ ≡ exec s (ys ++ x ∷ zs) f₁
exec-f₁≡ s f₁ x xs ys zs ∀₁ ≡₀ all₁ dsj | no f₁∉  = trans ≡₁ (trans (∀₁ f₁) ≡₂)
  where ≡₁ : exec s (xs ∷ʳ x) f₁ ≡ exec s xs f₁
        ≡₁ = sym (trans (St.lemma3 {exec s xs} f₁ (proj₂ (proj₁ (oracle x) (exec s xs))) f₁∉)
                        (cong-app (exec-∷ʳ s x xs) f₁))
        f₁∉₁ : f₁ ∉ cmdWriteNames x (exec s ys)
        f₁∉₁ = subst (λ x₁ → f₁ ∉ map proj₁ (proj₂ x₁)) ≡₀ f₁∉
        ≡₂ : exec s (ys ++ zs) f₁ ≡ exec s (ys ++ x ∷ zs) f₁
        ≡₂ with exec-∷≡ f₁ (exec s ys) (run x (exec s ys)) zs all₁ (St.lemma3 {exec s ys} f₁ (proj₂ (proj₁ (oracle x) (exec s ys))) f₁∉₁)
        ... | a = trans (cong-app (exec≡₄ {s} ys zs) f₁) (trans a (cong-app (exec≡₅ {s} x ys zs) f₁))
-- prove exec s (xs ∷ x) f₁ ≡ exec s xs f₁ ≡ exec s (ys ++ zs) f₁ ≡ exec s (xs ++ x ∷ ys) f₁

data DisjointBuild : System -> Build -> Set where
  Null : ∀ {s} → DisjointBuild s []
  Cons : ∀ {s} x -> Disjoint (cmdReadNames x s) (cmdWriteNames x s) -> (b : Build) -> DisjointBuild (run x s) b -> DisjointBuild s (x ∷ b)


dsj-≡ : ∀ s₁ s₂ b₁ → (∀ f₁ → s₂ f₁ ≡ s₁ f₁) → DisjointBuild s₁ b₁ → DisjointBuild s₂ b₁
dsj-≡ s₁ s₂ .[] ∀₁ Null = Null
dsj-≡ s₁ s₂ .(x ∷ b) ∀₁ (Cons x dsj b dsb) = Cons x (λ x₂ → dsj (v∈reads (proj₁ x₂) , v∈writes (proj₂ x₂))) b (dsj-≡ (run x s₁) (run x s₂) b (St.run-≡ x ∀₁) dsb)
  where ≡₁ : proj₁ (oracle x) s₂ ≡ proj₁ (oracle x) s₁
        ≡₁ = proj₂ (oracle x) s₂ s₁ λ f₁ x₁ → ∀₁ f₁
        v∈reads : ∀ {v} → v ∈ cmdReadNames x s₂ → v ∈ cmdReadNames x s₁
        v∈reads v∈ = subst (λ x₁ → _ ∈ x₁) (cong (map proj₁ ∘ proj₁) ≡₁) v∈
        v∈writes : ∀ {v} → v ∈ cmdWriteNames x s₂ → v ∈ cmdWriteNames x s₁
        v∈writes v∈ = subst (λ x₁ → _ ∈ x₁) (cong (map proj₁ ∘ proj₂) ≡₁) v∈

{-
hf-⊥ : {sys : System} {ls : List String} (f₁ : String) (b : Build) -> f₁ ∈ ls -> f₁ ∈ buildWriteNames sys b -> HazardFree sys b ls -> ⊥
hf-⊥ {sys} f₁ (x ∷ b) f₁∈ls f₁∈writes (HazardFree.Cons _ .x .b dsj hf) with ∈-++⁻ (Cwrites sys x) f₁∈writes
... | inj₁ ∈₁ = dsj (∈₁ , f₁∈ls)
... | inj₂ ∈₂ = hf-⊥ f₁ b (∈-++⁺ʳ (Creads sys x ++ Cwrites sys x) f₁∈ls) ∈₂ hf
-}

{- prove exec is equivalent when run in two different systems if ∀ f → f ∉ buildWrites x sys₁ -> sys₁ f ≡ sys₂ f -}
{-
exec≡-systems : {sys₁ sys₂ : System} {ls : List String} (b : Build) -> DisjointBuild sys₁ b -> HazardFree sys₁ b ls -> (∀ f₁ → f₁ ∉ writes sys₁ b → sys₁ f₁ ≡ sys₂ f₁) -> ∀ f₁ → exec sys₁ b f₁ ≡ exec sys₂ b f₁
exec≡-systems [] ds hf ∀₁ f₁ = ∀₁ f₁ λ ()
exec≡-systems {sys₁} {sys₂} (x ∷ b) (Cons .x dsj .b ds) (HazardFree.Cons _ .x .b x₁ hf) ∀₁ = exec≡-systems b ds hf λ f₁ x₂ → g₁ f₁ x₂
  where ⊥₁ : {f₂ : String} {ls₁ ls₂ : List String} -> f₂ ∈ ls₁ ++ ls₂ -> f₂ ∉ ls₁ -> f₂ ∉ ls₂ -> ⊥
        ⊥₁ f₂∈ f₂∉₁ f₂∉₂ with ∈-++⁻ _ f₂∈
        ... | inj₁ f₂∈₁ = f₂∉₁ f₂∈₁
        ... | inj₂ f₂∈₂ = f₂∉₂ f₂∈₂
        g₂ : (f₁ : String) -> f₁ ∈ map proj₁ (proj₁ (proj₁ (oracle x) sys₁)) -> f₁ ∉ writes sys₁ (x ∷ b)
        g₂ f₁ f₁∈ x₂ with ∈-++⁻ (map proj₁ (proj₂ (proj₁ (oracle x) sys₁))) x₂
        ... | inj₁ ∈₁ = dsj (f₁∈ , ∈₁)
        ... | inj₂ ∈₂ = hf-⊥ f₁ b (∈-++⁺ˡ (∈-++⁺ˡ f₁∈)) ∈₂ hf
        ≡₁ : proj₁ (oracle x) sys₁ ≡ proj₁ (oracle x) sys₂
        ≡₁ = proj₂ (oracle x) sys₁ sys₂ λ f₁ x₁ → ∀₁ f₁ (g₂ f₁ x₁)
        g₁ : (f₂ : String) -> f₂ ∉ writes (run oracle x sys₁) b -> run oracle x sys₁ f₂ ≡ run oracle x sys₂ f₂
        g₁ f₂ f₂∉ with f₂ ∈? map proj₁ (proj₂ (proj₁ (oracle x) sys₁))
        ... | yes f₂∈ = subst (λ x₁ → foldr St.extend sys₁ (proj₂ (proj₁ (oracle x) sys₁)) f₂ ≡ foldr St.extend sys₂ x₁ f₂) (cong proj₂ ≡₁) (St.lemma4 (proj₂ (proj₁ (oracle x) sys₁)) f₂ f₂∈)
        ... | no f₂∉₁ = St.lemma2 {oracle} {sys₁} {sys₂} x f₂ ≡₁ (∀₁ f₂ λ x₂ → ⊥₁ x₂ f₂∉₁ f₂∉)
-}

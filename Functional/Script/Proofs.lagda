
\begin{code}[hide]
open import Functional.State as St using (Oracle ; Cmd ; extend ; read ; Memory)

module Functional.Script.Proofs (oracle : Oracle) where

open import Agda.Builtin.Equality
open import Functional.State.Helpers (oracle) using (cmdWriteNames ; run ; cmdReadNames ; cmdWrites)
open import Functional.State.Properties (oracle) using (lemma5 ; lemma3)
open import Functional.Script.Exec (oracle) using (script ; buildWriteNames ; buildReadNames)
open import Functional.Script.Hazard (oracle) using (HazardFree ; FileInfo)
open import Functional.Script.Hazard.Properties (oracle) using (hf-∷ʳ-l ; hf-drop-mid ; hf=>disjoint ; hf=>disjointRW ; hf=>disjointWW ; hf=>disjointWR ; hf-∷ʳ-r)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Maybe using (just)
open import Data.List using (_∷ʳ_ ; List ; foldr)
open import Data.List.Properties using (unfold-reverse ; reverse-involutive ; ++-identityʳ ; length-reverse ; ∷-injectiveˡ ; ∷-injectiveʳ)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_ ; ↭-sym ; ↭-refl ; ↭-trans)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (Any-resp-↭ ; drop-mid ; ↭-length ; ∈-resp-↭ ; ++↭ʳ++)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique ; _∷_ ; head ; tail ; [])
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (++⁺)
open import Data.List using (map ; reverse ; length ; [] ; _∷_ ; _++_ ; [_])
open import Data.Product using (proj₁ ; proj₂ ; _,_)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Membership.Propositional using (_∈_ ; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-∃++ ; ∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any as Any using (here ; there)
open import Data.List.Relation.Unary.Any.Properties using (reverse⁺ ; reverse⁻)
open import Relation.Binary.PropositionalEquality using (subst ; subst₂ ; sym ; trans ; decSetoid ; cong-app ; cong) 
open import Data.List.Relation.Unary.All as All using (All ; _∷_ ; lookup)
open import Data.List.Relation.Unary.All.Properties as AllP hiding (++⁺)
open import Relation.Nullary using (¬_)
open import Functional.Build (oracle) using (Build ; UniqueEvidence ; PreCond)
open import Functional.Script.Properties (oracle) using (exec-f₁≡ ; exec-≡f₁ ; writes≡ ; exec-∷≡ ; exec≡₃)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.String.Properties using (_≟_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈?_)
open import Relation.Nullary using (yes ; no)
open import Data.Product.Properties using (,-injectiveʳ ; ,-injectiveˡ)
open import Relation.Nullary.Negation using (contradiction)
open import Function.Base using (_∘_)

{- If we follow the concept of hazardfree, it doesn't make sense, for 
  a hazardfree build to contain duplicates because those commands would need to do the
same thing, which would cause a hazard. + rattle doesn't run duplicates, so ....
lets just assume builds are unique. make my life easier...-}
all-drop-mid : ∀ (xs : Build) {ys} {x} {x₁} → All (λ y → ¬ x₁ ≡ y) (xs ++ x ∷ ys) → All (λ y → ¬ x₁ ≡ y) (xs ++ ys)
all-drop-mid [] all₁ = All.tail all₁
all-drop-mid (x₂ ∷ xs) all₁ = (All.head all₁) ∷ (all-drop-mid xs (All.tail all₁))

unique-drop-mid : ∀ (xs : Build) {ys} {x} → Unique (xs ++ x ∷ ys) → Unique (xs ++ ys)
unique-drop-mid [] (x₁ ∷ u) = u
unique-drop-mid (x₁ ∷ xs) u = (all-drop-mid xs (head u)) ∷ (unique-drop-mid xs (tail u))

unique→disjoint : ∀ {x₁ : Cmd} xs → All (λ y → ¬ x₁ ≡ y) xs → Disjoint xs (x₁ ∷ [])
unique→disjoint [] All.[] = λ ()
unique→disjoint (x ∷ xs) (¬x₁≡x ∷ all₁) x₂ = unique→disjoint xs all₁ (Any.tail (λ v≡x → ¬x₁≡x (trans (g₁ (proj₂ x₂)) v≡x)) (proj₁ x₂) , proj₂ x₂)
  where g₁ : ∀ {v} {x₁} → v ∈ x₁ ∷ [] → x₁ ≡ v
        g₁ (here px) = sym px

all-reverse : ∀ {x₁ : Cmd} xs → All (λ y → ¬ x₁ ≡ y) xs → All (λ y → ¬ x₁ ≡ y) (reverse xs)
all-reverse [] All.[] = All.[]
all-reverse (x ∷ xs) (px ∷ all₁) = subst (λ x₂ → All (λ y → ¬ _ ≡ y) x₂) (sym (unfold-reverse x xs)) (AllP.++⁺ (all-reverse xs all₁) (px ∷ All.[]))

unique=>∉ : ∀ (x : Cmd) xs → All (λ y → ¬ x ≡ y) xs → x ∉ xs
unique=>∉ x xs px x₁ with lookup px x₁
... | a = a refl

unique=>¬ : ∀ (v : Cmd) x xs ys → v ∈ ys → Unique (xs ++ x ∷ ys) → ¬ v ≡ x
unique=>¬ v x [] ys v∈ys (px ∷ u) = λ x₁ → (lookup px v∈ys) (sym x₁)
unique=>¬ v x (x₁ ∷ xs) ys v∈ys (px ∷ u) = unique=>¬ v x xs ys v∈ys u

unique-reverse : ∀ xs → Unique xs → Unique (reverse xs)
unique-reverse [] u = []
unique-reverse (x₁ ∷ xs) (px ∷ u) with ++⁺ (unique-reverse xs u) (All.[] ∷ []) (unique→disjoint (reverse xs) (all-reverse xs px))
... | u₁ = subst (λ ls → Unique ls) (sym (unfold-reverse x₁ xs)) u₁

↭-reverse : ∀ (xs : Build) → xs ↭ reverse xs
↭-reverse xs = subst (λ x → x ↭ reverse xs) (++-identityʳ xs) (++↭ʳ++ xs [])

helper5 : ∀ {s} xs x → Disjoint (cmdWriteNames x s) xs → All (λ f₁ → s f₁ ≡ run x s f₁) xs
helper5 [] x dsj = All.[]
helper5 {s} (x₁ ∷ xs) x dsj = (lemma3 x₁ (cmdWrites x s) λ x₂ → dsj (x₂ , here refl)) All.∷ (helper5 xs x λ x₂ → dsj ((proj₁ x₂) , there (proj₂ x₂)))

-- kind of a dumb function that could be inlined?
helper4 : ∀ {f₁} {s} bs x → f₁ ∈ cmdReadNames x s → Disjoint (cmdReadNames x s) (buildWriteNames s bs) → f₁ ∉ buildWriteNames s bs
helper4 bs x f₁∈reads dsj f₁∈writes = dsj (f₁∈reads , f₁∈writes)

helper3 : ∀ {s} as bs xs x → Disjoint (cmdReadNames x (script as s)) (buildWriteNames (script as s) bs) → (∀ f₁ → script (as ++ bs) s f₁ ≡ script xs s f₁) → proj₁ (oracle x) (script as s) ≡ proj₁ (oracle x) (script xs s)
helper3 {s} as bs xs x dsj ∀₁ = proj₂ (oracle x) (script as s) (script xs s) λ f₁ x₁ → trans (exec-≡f₁ s f₁ as bs (f₁∉₁ x₁)) (∀₁ f₁)
  where f₁∉₁ : ∀ {f₁} → f₁ ∈ cmdReadNames x (script as s) → f₁ ∉ buildWriteNames (script as s) bs
        f₁∉₁ f₁∈reads = helper4 bs x f₁∈reads dsj

helper8 : ∀ {s} {f₁} xs → f₁ ∉ (buildWriteNames s xs) → script xs s f₁ ≡ s f₁
helper8 [] f₁∉ = refl
helper8 {s} {f₁} (x ∷ xs) f₁∉ = trans (helper8 xs λ x₁ → f₁∉ (∈-++⁺ʳ (cmdWriteNames x s) x₁))
                                      (sym (lemma3 f₁ (cmdWrites x s) λ x₁ → f₁∉ (∈-++⁺ˡ x₁)))

helper7 : ∀ {s} {s₁} f₁ xs ys → xs ≡ ys → f₁ ∈ map proj₁ xs → foldr extend s xs f₁ ≡ foldr extend s₁ ys f₁
helper7 g₁ ((f , v) ∷ xs) ((f₁ , v₁) ∷ ys) ≡₁ f₁∈ with f ≟ g₁ | f₁ ≟ g₁
... | yes f≡g₁ | yes f₁≡g₁ = cong just (,-injectiveʳ (∷-injectiveˡ ≡₁))
... | yes f≡g₁ | no ¬f₁≡g₁ = contradiction (trans (sym (,-injectiveˡ (∷-injectiveˡ ≡₁))) f≡g₁) ¬f₁≡g₁
... | no ¬f≡g₁ | yes f₁≡g₁ = contradiction (trans (,-injectiveˡ (∷-injectiveˡ ≡₁)) f₁≡g₁) ¬f≡g₁
... | no ¬f≡g₁ | no ¬f₁≡g₁ = helper7 g₁ xs ys (∷-injectiveʳ ≡₁) (Any.tail (λ x → ¬f≡g₁ (sym x)) f₁∈)

script≡ : ∀ {s} xs ys → script (xs ++ ys) s ≡ script ys (script xs s)
script≡ [] ys = refl
script≡ (x ∷ xs) ys = script≡ xs ys

-- putting x in middle doesnt change result if x doesnt write to file. 
helper6 : ∀ {s} {f₁} xs x → f₁ ∉ cmdWriteNames x s → All (λ f₁ → s f₁ ≡ run x s f₁) (buildReadNames (run x s) xs) → script (x ∷ xs) s f₁ ≡ script xs s f₁
helper6 {s} xs x f₁∉ all₁ = sym (exec-∷≡ _ s (run x s) xs all₁ (lemma3 _ (cmdWrites x s) f₁∉))


add-back : ∀ {s} as bs xs x → Disjoint (cmdWriteNames x (script as s)) (buildWriteNames (run x (script as s)) bs) → Disjoint (cmdReadNames x (script as s)) (buildWriteNames (run x (script as s)) bs) → Disjoint (cmdWriteNames x (script as s)) (buildReadNames (run x (script as s)) bs) → (∀ f₁ → script (as ++ bs) s f₁ ≡ script xs s f₁) → (∀ f₁ → script (as ++ x ∷ bs) s f₁ ≡ script (xs ++ x ∷ []) s f₁)
add-back {s} as bs xs x dsj₀ dsj dsj₁ ∀₁ f₁ with helper5 (buildReadNames (run x (script as s)) bs) x dsj₁
... | all₁ with writes≡ (script as s) (run x (script as s)) bs all₁
... | ≡₁   with helper3 as bs xs x (subst (λ x₁ → Disjoint _ x₁) (sym ≡₁) dsj) ∀₁
... | x≡   with f₁ ∈? cmdWriteNames x (script as s)
-- we know as ++ x ≡ xs ++ x. just show bs doesnt change what x wrote to.
... | yes f₁∈ = trans ≡₂ ≡₃
  where ≡₂ : script (as ++ x ∷ bs) s f₁ ≡ run x (script as s) f₁
        ≡₂ = trans (cong-app (script≡ as (x ∷ bs)) f₁) (helper8 bs λ x₁ → dsj₀ (f₁∈ , x₁))
        ≡₃ : run x (script as s) f₁ ≡ script (xs ++ x ∷ []) s f₁
        ≡₃ = trans (helper7 {script as s} {script xs s} f₁ (cmdWrites x (script as s)) (cmdWrites x (script xs s)) (cong proj₂ x≡) f₁∈)
                   (sym (cong-app (script≡ xs (x ∷ [])) f₁))
        
... | no f₁∉ with trans (cong-app (script≡ as (x ∷ bs)) f₁) (trans (helper6 bs x f₁∉ all₁) (sym (cong-app (script≡ as bs) f₁)))
                  -- script xs s f₁ ≡ script (xs ++ x ∷ []) s f₁
... | ≡₂     with trans (lemma3 _ (cmdWrites x (script xs s)) (subst (λ x₁ → _ ∉ x₁) (cong (map proj₁ ∘ proj₂) x≡) f₁∉)) (cong-app (exec≡₃ x xs) f₁)
... | ≡₃ = trans ≡₂ (trans (∀₁ f₁) ≡₃)


reordered : ∀ {s} {ls} xs ys → length xs ≡ length ys → xs ↭ ys → UniqueEvidence xs ys (map proj₁ ls)
           → HazardFree s xs (reverse ys) ls → (∀ f₁ → script xs s f₁ ≡ script (reverse ys) s f₁)
reordered [] [] _ p _ hf f₁ = refl
reordered {s} {ls} xs (x ∷ ys) _ p (uxs , ux ∷ uys , uls , dsj) hf f₁ with ∈-∃++ (∈-resp-↭ (↭-sym p) (here refl))
... | (as , bs , ≡₁) with add-back as bs (reverse ys) x dsj₁ dsj₂ dsj₃ (reordered (as ++ bs) ys (↭-length ↭₂) ↭₂ (uas++bs , uys , uls , dsj₀) hf₁)
  where ↭₂ : as ++ bs ↭ ys
        ↭₂ = drop-mid as [] (subst (λ x₁ → x₁ ↭ x ∷ ys) ≡₁ p)
        uas++bs : Unique (as ++ bs)
        uas++bs = unique-drop-mid as (subst (λ x₁ → Unique x₁) ≡₁ uxs)
        dsj₀ : Disjoint (as ++ bs) (map proj₁ ls)
        dsj₀ x₂ with ∈-++⁻ as (proj₁ x₂)
        ... | inj₁ _∈as = dsj (subst (λ x₁ → _ ∈ x₁) (sym ≡₁) (∈-++⁺ˡ _∈as) , (proj₂ x₂))
        ... | inj₂ _∈bs = dsj (subst (λ x₁ → _ ∈ x₁) (sym ≡₁) (∈-++⁺ʳ as (there _∈bs)) , (proj₂ x₂))
        ⊆₁ : as ++ x ∷ bs ⊆ reverse ys ++ x ∷ []
        ⊆₁ x₁∈as++x∷bs = subst (λ x₂ → _ ∈ x₂)
                               (unfold-reverse x ys)
                               (reverse⁺ (∈-resp-↭ p (subst (λ x₂ → _ ∈ x₂) (sym ≡₁) x₁∈as++x∷bs)))
        hf₀ : HazardFree s (as ++ x ∷ bs) ((reverse ys) ++ x ∷ []) _
        hf₀ = subst₂ (λ x₂ x₃ → HazardFree s x₂ x₃ _) ≡₁ (unfold-reverse x ys) hf
        hf₁ : HazardFree s (as ++ bs) (reverse ys) _
        hf₁ = hf-drop-mid as bs (reverse ys) ⊆₁
                          (subst (λ x₁ → Unique x₁) ≡₁ uxs)
                          (subst (λ x₁ → Unique x₁) (unfold-reverse x ys) (unique-reverse (x ∷ ys) (ux ∷ uys)))
                          uls
                          (subst (λ x₁ → Disjoint x₁ _) ≡₁ dsj)
                          hf₀
        bs⊆reverse-ys : bs ⊆ reverse ys
        bs⊆reverse-ys x₃ = reverse⁺ (∈-resp-↭ ↭₂ (∈-++⁺ʳ as x₃))
        x∉reverse-ys : x ∉ reverse ys
        x∉reverse-ys x∈reverse-ys = lookup ux (reverse⁻ x∈reverse-ys) refl
        dsj₁ : Disjoint (cmdWriteNames x (script as _)) (buildWriteNames (run x (script as _)) bs)
        dsj₁ = hf=>disjointWW s x as bs (reverse ys) _  bs⊆reverse-ys x∉reverse-ys hf₀
        dsj₂ : Disjoint (cmdReadNames x (script as _)) (buildWriteNames (run x (script as _)) bs)
        dsj₂ = hf=>disjointRW s x as bs (reverse ys) _ bs⊆reverse-ys x∉reverse-ys hf₀
        dsj₃ : Disjoint (cmdWriteNames x (script as _)) (buildReadNames (run x (script as _)) bs)
        dsj₃ = hf=>disjointWR s x as bs (reverse ys) _ bs⊆reverse-ys x∉reverse-ys hf₀
... | ∀₂ = subst₂ (λ x₂ x₃ → script x₂ _ f₁ ≡ script x₃ _ f₁) (sym ≡₁) (sym (unfold-reverse x ys)) (∀₂ f₁)
\end{code}

\newcommand{\reordered}{%
\begin{code}
reordered≡ : ∀ s br bc → PreCond s br bc → HazardFree s br bc []
           → (∀ f₁ → script bc s f₁ ≡ script br s f₁)
\end{code}}
\begin{code}[hide]
reordered≡ s br bc (dsb , ubr , ubc , pm) hf₁ with reordered {s} br (reverse bc) (↭-length br↭reverse-bc) br↭reverse-bc ue (subst (λ x → HazardFree s br x _) (sym (reverse-involutive bc)) hf₁)
  where br↭reverse-bc : br ↭ reverse bc
        br↭reverse-bc = ↭-trans (↭-sym pm) (↭-reverse bc)
        g₁ : Disjoint br []
        g₁ ()
        ue : UniqueEvidence br (reverse bc) []
        ue = ubr , (unique-reverse bc ubc) , [] , g₁
... | ∀₁ = λ f₁ → subst (λ x → script x s f₁ ≡ script br s f₁) (reverse-involutive bc) (sym (∀₁ f₁))
\end{code}

{-# OPTIONS --allow-unsolved-metas #-}
open import Functional.State using (Oracle ; Cmd)

module Functional.Script.Hazard.Properties (oracle : Oracle) where
open import Functional.State.Properties (oracle) as St hiding (lemma3 ; lemma4 ; lemma2)
open import Functional.State.Helpers (oracle) using (run ; cmdWriteNames ; cmdReadNames)
open import Functional.Script.Exec (oracle) using (script ; buildReadNames ; buildWriteNames)
open import Functional.Build (oracle) using (Build)
open import Common.List.Properties using (_before_∈_)
open import Agda.Builtin.Equality
open import Functional.File using (FileName)
open import Functional.Script.Hazard.Base (oracle) using (HazardFree ; [] ; _∷_ ; files ; cmdsRun ; cmdWrote ; FileInfo ; save ; filesRead ; ∈-files-++ ; ∈-filesRead-++ ; ∈-filesWrote-++ ; ∈-cmdRead++mid ; ∈-cmdWrote++mid ; ∈-cmdWrote∷ ; ∈-cmdRead∷l ; lemma2 ; cmdWrote∷-≡ ; Hazard ; ∈-cmdWrote∷l ; Speculative ; ReadWrite ; WriteWrite ; cmdRead ; filesWrote) 
open import Data.List as L using (_∷_ ; _++_ ; map ; foldr ; List ; foldl ; _∷ʳ_ ; [] ; reverse ; [_])
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; _×_ ; Σ-syntax ; ∃-syntax ; map₁)
open import Relation.Binary.PropositionalEquality using (subst ; subst₂ ; cong ; sym ; trans ; cong₂)
open import Function using (_∘_)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Membership.Propositional using (_∈_ ; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-∃++)
open import Data.String using (String)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List.Properties using (map-++-commute ; ++-assoc ; reverse-involutive ; ∷-injectiveˡ ; ∷-injectiveʳ ; reverse-++-commute ; unfold-reverse ; ++-identityˡ)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (Any-resp-⊆ ; ++⁺ ; ⊆-refl ; xs⊆ys++xs)
open import Data.List.Relation.Unary.AllPairs using (AllPairs ; _∷_)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Relation.Nullary using (¬_ ; yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Data.List.Relation.Unary.Any.Properties using (reverse⁺ ; reverse⁻)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.String.Properties using (_≟_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.Empty using (⊥)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)

{- what does memoize do about duplicates? 

  The following property is nice: build is idempotent

    
  
  #1 write #2 

  #2 write ()

  we shouldn't care about forward builds with duplicate commands; because builds can't be idempotent 

-}

-- need some more evidence. need to know x₂ ¬≡ x
¬bf-∷ʳ : ∀ (x : Cmd) x₁ {x₂} b₁ → ¬ x₂ ≡ x → ¬ x₁ before x₂ ∈ b₁ → ¬ x₁ before x₂ ∈ (b₁ ∷ʳ x)
¬bf-∷ʳ x x₁ {x₂} b₁ ¬x₂≡x ¬bf (xs , ys , b₁∷ʳx≡xs++x₁∷ys , x₂∈ys) with g₁ (reverse b₁) (reverse ys) (reverse xs) x₂ x x₁ ≡₁ (reverse⁺ x₂∈ys) ¬x₂≡x
    where g₁ : ∀ b₁ ys xs x₂ x x₁ → x ∷ b₁ ≡ ys ∷ʳ x₁ ++ xs → x₂ ∈ ys → ¬ x₂ ≡ x → ∃[ zs ](b₁ ≡ zs ∷ʳ x₁ ++ xs × x₂ ∈ zs)
          g₁ b₁ (x₃ ∷ ys) xs x₂ x x₁ ≡₁ x₂∈ys ¬x₂≡x = ys , ∷-injectiveʳ ≡₁ , tail (λ x₂≡x₃ → ¬x₂≡x (trans x₂≡x₃ (sym (∷-injectiveˡ ≡₁)))) x₂∈ys
          ≡₁ : x ∷ reverse b₁ ≡ reverse ys ∷ʳ x₁ ++ reverse xs
          ≡₁ = trans (sym (reverse-++-commute b₁ (x ∷ []))) (trans (cong reverse b₁∷ʳx≡xs++x₁∷ys) (trans (reverse-++-commute xs (x₁ ∷ ys)) (cong (_++ reverse xs) (unfold-reverse x₁ ys))))
... | zs , ≡₃ , x₂∈zs = ¬bf (xs , reverse zs , ≡₂ , reverse⁺ x₂∈zs)
  where ≡₂ : b₁ ≡ xs ++ x₁ ∷ reverse zs
        ≡₂ = trans (sym (reverse-involutive b₁))
                   (trans (cong reverse ≡₃)
                          (trans (reverse-++-commute (zs ∷ʳ x₁) (reverse xs))
                                 (cong₂ _++_ (reverse-involutive xs) (reverse-++-commute zs (x₁ ∷ [])))))

unique→¬≡ : ∀ ls (x₁ : Cmd) {x} → x₁ ∈ ls → Unique (ls ∷ʳ x) → ¬ x₁ ≡ x
unique→¬≡ (x ∷ ls) x₁ x₁∈ls (px ∷ u) with x₁ ≟ x
... | yes x₁≡x = λ x₁≡x₂ → lookup px (∈-++⁺ʳ ls (here refl)) (trans (sym x₁≡x) x₁≡x₂)
unique→¬≡ (x ∷ ls) x₁ x₁∈ls (px ∷ u) | no ¬x₁≡x = unique→¬≡ ls x₁ (tail ¬x₁≡x x₁∈ls) u

{-
¬sh-∷ʳ : ∀ b₁ x {ls} → Unique (b₁ ∷ʳ x) → ¬SpeculativeHazard (b₁ ∷ʳ x) ls → ¬SpeculativeHazard b₁ ls
¬sh-∷ʳ b₁ x u ¬sh = λ x₁ x₂ x₃ x₄ x₅ x₆ → ¬sh x₁ x₂ x₃ (∈-++⁺ˡ x₄) (¬bf-∷ʳ x x₁ b₁ (unique→¬≡ b₁ x₂ x₄ u) x₅) x₆ -}

hf-∷ʳ-l : ∀ {s} b₁ {b₂} {x} {ls} → HazardFree s (b₁ ∷ʳ x) b₂ ls → HazardFree s b₁ b₂ ls
hf-∷ʳ-l List.[] hf = []
hf-∷ʳ-l (x ∷ b₁) (¬hz ∷ hf) = ¬hz ∷ (hf-∷ʳ-l b₁ hf)

¬hz-∷ʳ-r : ∀ {s} {x} {b} {x₁} {ls} → Unique (b ∷ʳ x₁) → ¬ Hazard s x (b ∷ʳ x₁) ls → ¬ Hazard s x b ls
¬hz-∷ʳ-r u ¬hz (Speculative x₀ x₂ y x₃ x₄ x₅ x₆)
  = ¬hz (Speculative x₀ x₂ y (∈-++⁺ˡ x₃) (¬bf-∷ʳ _ _ _ (unique→¬≡ _ _ x₃ u) x₄) x₅ x₆)
¬hz-∷ʳ-r u ¬hz (ReadWrite x x₁) = ¬hz (ReadWrite x x₁)
¬hz-∷ʳ-r u ¬hz (WriteWrite x x₁) = ¬hz (WriteWrite x x₁)


hf-∷ʳ-r : ∀ {s} b₁ b₂ {x} {ls} → Unique (b₂ ∷ʳ x) → HazardFree s b₁ (b₂ ∷ʳ x) ls → HazardFree s b₁ b₂ ls
hf-∷ʳ-r [] b₂ u hf = []
hf-∷ʳ-r (x ∷ b₁) b₂ u (¬hz ∷ hf)
  = (¬hz-∷ʳ-r u ¬hz) ∷ (hf-∷ʳ-r b₁ b₂ u hf)

disjoint-drop-mid : ∀ ls xs ys zs → Disjoint ls (files (xs ++ ys ++ zs)) → Disjoint ls (files (xs ++ zs))
disjoint-drop-mid ls xs ys zs dsj = λ x → dsj (proj₁ x , ∈-files-++ xs ys zs (proj₂ x))


before-add-mid : ∀ x₂ x₁ (xs : Build) ys zs → x₂ before x₁ ∈ (xs ++ zs) → x₂ before x₁ ∈ (xs ++ ys ++ zs)
before-add-mid x₂ x₁ [] ys zs (as , bs , zs≡as++x₂∷bs , x₁∈bs)
  = ys ++ as , bs , ≡₁ , x₁∈bs
    where ≡₁ : ys ++ zs ≡ (ys ++ as) ++ x₂ ∷ bs
          ≡₁ = trans (cong (ys ++_) zs≡as++x₂∷bs) (sym (++-assoc ys as (x₂ ∷ bs)))
before-add-mid x₂ x₁ (x ∷ xs) ys zs ([] , bs , x∷xs++zs≡x₂∷bs , x₁∈bs)
  = [] , xs ++ ys ++ zs , cong (_∷ xs ++ ys ++ zs) (∷-injectiveˡ x∷xs++zs≡x₂∷bs) , ∈₁
    where ∈₁ : x₁ ∈ xs ++ ys ++ zs
          ∈₁ with ∈-++⁻ xs (subst (λ x₃ → x₁ ∈ x₃) (sym (∷-injectiveʳ x∷xs++zs≡x₂∷bs)) x₁∈bs)
          ... | inj₁ x₁∈xs = ∈-++⁺ˡ x₁∈xs
          ... | inj₂ x₁∈zs = ∈-++⁺ʳ xs (∈-++⁺ʳ ys x₁∈zs)
before-add-mid x₂ x₁ (x ∷ xs) ys zs (x₃ ∷ as , bs , x∷xs++zs≡x₃∷as++x₂∷bs , x₁∈bs) with before-add-mid x₂ x₁ xs ys zs (as , bs , ∷-injectiveʳ x∷xs++zs≡x₃∷as++x₂∷bs , x₁∈bs)
... | cs , ds , xs++ys≡cs++x₂∷ds , x₁∈ds = x ∷ cs , ds , cong (x ∷_) xs++ys≡cs++x₂∷ds , x₁∈ds

¬Hazard-drop-mid : ∀ {s} {x} {b₂} xs ys zs → Unique (x ∷ cmdsRun (xs ++ ys ++ zs)) → ¬ Hazard s x b₂ (xs ++ ys ++ zs) → ¬ Hazard s x b₂ (xs ++ zs)
¬Hazard-drop-mid xs ys zs u ¬hz (ReadWrite x x₁)
  = ¬hz (ReadWrite x (∈-filesRead-++ xs ys zs x₁))
¬Hazard-drop-mid xs ys zs u ¬hz (WriteWrite x x₁)
  = ¬hz (WriteWrite x (∈-filesWrote-++ xs ys zs x₁))
¬Hazard-drop-mid {s} {x} xs ys zs u ¬hz (Speculative x₁ x₂ y x₃ x₄ x₅ x₆)
  = ¬hz (Speculative x₁ x₂ bf x₃ x₄ (∈-cmdRead++mid x₂ (save s x xs) ys zs u x₅) (∈-cmdWrote++mid x₁ (save s x xs) ys zs u x₆))
    where bf₁ : x₂ before x₁ ∈ (x ∷ cmdsRun xs ++ cmdsRun zs)
          bf₁ = subst (λ x₇ → x₂ before x₁ ∈ x₇) (cong (x ∷_) (map-++-commute proj₁ xs zs)) y
          bf : x₂ before x₁ ∈ (x ∷ cmdsRun (xs ++ ys ++ zs))
          bf with (before-add-mid x₂ x₁ (x ∷ cmdsRun xs) (cmdsRun ys) (cmdsRun zs) bf₁)
          ... | a = subst (λ x₇ → x₂ before x₁ ∈ x₇) (sym (trans (cong (x ∷_) (map-++-commute proj₁ xs (ys ++ zs))) (cong ((x ∷ (map proj₁ xs)) ++_) (map-++-commute proj₁ ys zs)))) a

hazard-still : ∀ {s} {s₁} {x} {b} {ls} → proj₁ (oracle x) s ≡ proj₁ (oracle x) s₁ → Hazard s x b ls → Hazard s₁ x b ls
hazard-still ≡₁ (ReadWrite x x₁)
  = ReadWrite (subst (λ x₃ → _ ∈ x₃) (cong (map proj₁ ∘ proj₂) ≡₁) x) x₁
hazard-still ≡₁ (WriteWrite x x₁)
  = WriteWrite (subst (λ x₃ → _ ∈ x₃) (cong (map proj₁ ∘ proj₂) ≡₁) x) x₁
hazard-still {s} {s₁} {x} ≡₁ (Speculative {s} {x} {b} {ls} {v} x₁ x₂ y x₃ x₄ x₅ x₆)
  = Speculative x₁ x₂ y x₃ x₄ (subst (λ x₈ → v ∈ cmdRead x₈ x₂) (cong (_∷ _) ≡₂) x₅) (subst (λ x₈ → v ∈ cmdWrote x₈ x₁) (cong (_∷ _) ≡₂) x₆)
    where ≡₂ : (x , cmdReadNames x s , cmdWriteNames x s) ≡ (x , cmdReadNames x s₁ , cmdWriteNames x s₁)
          ≡₂ = cong (x ,_) (cong₂ _,_ (cong (map proj₁ ∘ proj₁) ≡₁) (cong (map proj₁ ∘ proj₂) ≡₁))
 
-- there is a copy of this elsewhere so maybe organize this better.
g₂ : ∀ {x : Cmd} xs → x ∉ xs → All (λ y → ¬ x ≡ y) xs
g₂ [] x∉xs = All.[]
g₂ (x ∷ xs) x∉xs = (λ x₃ → x∉xs (here x₃)) All.∷ (g₂ xs λ x₃ → x∉xs (there x₃))

hf-still : ∀ {s₁} {s} b₁ {b₂} xs ys zs → (∀ f₁ → f₁ ∈ buildReadNames s₁ b₁ → s₁ f₁ ≡ s f₁) → Unique b₁ → Unique (map proj₁ (xs ++ ys ++ zs)) → Disjoint b₁ (map proj₁ (xs ++ ys ++ zs)) → HazardFree s₁ b₁ b₂ (xs ++ ys ++ zs) → HazardFree s b₁ b₂ (xs ++ zs)
hf-still [] xs ys zs ∀₁ ub₁ u dsj hf = []
hf-still {s₁} {s} (x ∷ b₁) xs ys zs ∀₁ (px ∷ ub₁) u dsj (¬hz ∷ hf)
  = ¬hz₁ ∷ (hf-still b₁ (save s x xs) ys zs ∀₂ ub₁ u₂ dsj₁ hf₂) 
    where dsj₁ : Disjoint b₁ (x ∷ map proj₁ (xs ++ ys ++ zs))
          dsj₁ = λ x₁ → dsj (there (proj₁ x₁) , tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
          ≡₀ : proj₁ (oracle x) s₁ ≡ proj₁ (oracle x) s
          ≡₀ = (proj₂ (oracle x) s₁ s λ f₁ x₃ → ∀₁ f₁ (∈-++⁺ˡ x₃))
          ≡₁ : cmdWriteNames x s₁ ≡ cmdWriteNames x s
          ≡₁ = cong (map proj₁ ∘ proj₂) ≡₀
          ≡₂ : cmdReadNames x s₁ ≡ cmdReadNames x s
          ≡₂ = cong (map proj₁ ∘ proj₁) ≡₀
          hf₂ : HazardFree (run x s₁) b₁ _ ((x , cmdReadNames x s , cmdWriteNames x s) ∷ xs ++ ys ++ zs)
          hf₂ = subst (λ x₃ → HazardFree (run x s₁) b₁ _ (x₃ ∷ xs ++ ys ++ zs))
                      (cong (x ,_) (cong₂ _,_ ≡₂ ≡₁)) hf
          ∀₂ : ∀ f₁ → f₁ ∈ buildReadNames (run x s₁) b₁ → run x s₁ f₁ ≡ run x s f₁
          ∀₂ f₁ f₁∈ with ∀₁ f₁ (∈-++⁺ʳ (cmdReadNames x s₁) f₁∈)
          ... | s₁f₁≡sf₁ = St.lemma2 ≡₀ s₁f₁≡sf₁
          u₂ : Unique (x ∷ (map proj₁ (xs ++ ys ++ zs)))
          u₂ = (g₂ (map proj₁ (xs ++ ys ++ zs)) λ x₁ → dsj (here refl , x₁)) ∷ u
          ¬hz₁ : ¬ Hazard s x _ (xs ++ zs)
          ¬hz₁ hz with ¬Hazard-drop-mid xs ys zs u₂ ¬hz
          ... | a = a (hazard-still (sym ≡₀) hz)

lemma3 : ∀ {s} {x} {ls} → Disjoint (cmdWriteNames x s) ls → (∀ f₁ → f₁ ∈ ls → run x s f₁ ≡ s f₁)
lemma3 {s} {x} dsj f₁ f₁∈ls with f₁ ∈? cmdWriteNames x s
... | yes f₁∈ = contradiction (f₁∈ , f₁∈ls) dsj
... | no f₁∉ = sym (St.lemma3 f₁ (proj₂ (proj₁ (oracle x) s)) f₁∉)


g₃ : ∀ {x} {b₁} (ys : Build) {xs} {x₁} {x₂} → x ∷ b₁ ≡ ys ∷ʳ x₁ ++ xs → x₂ ∈ ys → x₁ ∈ b₁
g₃ (x ∷ ys) ≡₁ x₂∈ys
  = subst (λ x₄ → _ ∈ x₄) (sym (∷-injectiveʳ ≡₁)) (∈-++⁺ˡ (∈-++⁺ʳ ys (here refl)))


g₄ : ∀ {x : Cmd} {x₁} {ls} → x ∈ ls → x₁ ∉ ls → ¬ x ≡ x₁
g₄ x∈ls x₁∉ls = λ x≡x₁ → x₁∉ls (subst (λ x₄ → x₄ ∈ _) x≡x₁ x∈ls)

{- We still need to know: 
 2. we need to know x₃ ¬≡ x ; 
-}
lemma4 : ∀ {s} {x} ys {b₁} {ls} → x ∉ ys → ys ⊆ (b₁ ∷ʳ x) → Unique (b₁ ∷ʳ x) → HazardFree s ys (b₁ ∷ʳ x) ls → Disjoint (cmdWrote ls x) (buildReadNames s ys)
lemma4 [] x∉ys ⊆₁ u [] = λ ()
lemma4 {s} {x} (x₃ ∷ b₂) {b₁} x∉ys ⊆₁ u (¬hz ∷ hf) x₄ with ∈-++⁻ (cmdReadNames x₃ s) (proj₂ x₄)
... | inj₁ v∈₁ = ¬hz (Speculative x x₃ ([] , map proj₁ _ , refl , lemma2 x _ (proj₁ x₄)) (⊆₁ (here refl)) ¬bf (∈-cmdRead∷l x₃i _ v∈₁) (∈-cmdWrote∷ x₃i x _ (proj₁ x₄) (g₄ (here refl) x∉ys)))
  where x₃i : (Cmd × List FileName × List FileName)
        x₃i = (x₃ , (cmdReadNames x₃ s) , (cmdWriteNames x₃ s))
        ¬bf : ¬ x before x₃ ∈ (_ ∷ʳ x)
        ¬bf (xs , ys , b₁∷ʳx≡xs++x∷ys , x₃∈ys) = contradiction refl (unique→¬≡ b₁ x (reverse⁻ (g₃ (reverse ys) ≡₂ (reverse⁺ x₃∈ys))) u)
          where ≡₂ : x ∷ reverse b₁ ≡ reverse ys ∷ʳ x ++ reverse xs
                ≡₂ = trans (sym (reverse-++-commute b₁ [ x ]))
                           (trans (cong reverse b₁∷ʳx≡xs++x∷ys)
                                  (trans (reverse-++-commute xs (x ∷ ys))
                                         (cong (_++ reverse xs) (unfold-reverse x ys))))
... | inj₂ v∈₂ = (lemma4 b₂ (λ x₁ → x∉ys (there x₁)) (λ x₁ → ⊆₁ (there x₁)) u hf) (∈-cmdWrote∷ x₃i x _ (proj₁ x₄) (g₄ (here refl) x∉ys) , v∈₂)
  where x₃i : (Cmd × List FileName × List FileName)
        x₃i = (x₃ , (cmdReadNames x₃ s) , (cmdWriteNames x₃ s))

g₅ : ∀ (x : Cmd) ys → All (λ y → ¬ x ≡ y) ys → x ∉ ys
g₅ x [] All.[] = λ ()
g₅ x (x₁ ∷ ys) (¬x≡x₁ All.∷ all₁) x∈x₁∷xs = g₅ x ys all₁ (tail ¬x≡x₁ x∈x₁∷xs)

{- x∈x₁∷xs with x ≟ x₁
... | yes x≡x₁ = contradiction x≡x₁ ¬x≡x₁
... | no _ = {!!} -}


-- we need to know x doesnt write to anything read by ys a command in ys.
-- we should know this from the ¬ speculative hazard info and ?
hf-drop-mid : ∀ {s} xs ys b₁ {x} {ls} → xs ++ x ∷ ys ⊆ b₁ ∷ʳ x → Unique (xs ++ x ∷ ys) → Unique (b₁ ∷ʳ x) → Unique (map proj₁ ls) → Disjoint (xs ++ x ∷ ys) (map proj₁ ls) → HazardFree s (xs ++ x ∷ ys) (b₁ ∷ʳ x) ls → HazardFree s (xs ++ ys) b₁ ls
hf-drop-mid {s} List.[] List.[] b₁ ⊆₁ u₁ u uls dsj hf = []
hf-drop-mid {s} List.[] ys b₁ {x} ⊆₁ (px₁ ∷ u₁) u uls dsj (¬hz ∷ hf) with hf-still ys [] [ (x , (cmdReadNames x s) , (cmdWriteNames x s)) ] _ ∀₁ u₁ uls₂ dsj₁ hf
  where dsj₁ : Disjoint ys (x ∷ map proj₁ _)
        dsj₁ = λ x₁ → dsj (there (proj₁ x₁) , tail (λ v≡x → lookup px₁ (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
        uls₂ : Unique (x ∷ map proj₁ _)
        uls₂ = g₂ (map proj₁ _) (λ x₁ → dsj (here refl , x₁)) ∷ uls
        ∀₁ : ∀ f₁ → f₁ ∈ buildReadNames (run x s) ys → run x s f₁ ≡ s f₁
        ∀₁ = lemma3 (subst (λ x₁ → Disjoint x₁ (buildReadNames (run x s) ys)) (cmdWrote∷-≡ (x , (cmdReadNames x s) , (cmdWriteNames x s)) _) (lemma4 ys (g₅ x ys px₁) (λ x₁ → ⊆₁ (there x₁)) u hf))
... | hf₂ = hf-∷ʳ-r ys b₁ u hf₂
hf-drop-mid (x₁ ∷ xs) ys b₁ {x} ⊆₁ (px₁ ∷ u₁) u uls dsj (¬hz ∷ hf)
  = (¬hz-∷ʳ-r u ¬hz) ∷ (hf-drop-mid xs ys b₁ (λ x₃ → ⊆₁ (there x₃)) u₁ u uls₂ dsj₁ hf)
    where dsj₁ : Disjoint (xs ++ x ∷ ys) (x₁ ∷ map proj₁ _)
          dsj₁ = λ x₃ → dsj (there (proj₁ x₃) , tail (λ v≡x₁ → lookup px₁ (proj₁ x₃) (sym v≡x₁)) (proj₂ x₃))
          uls₂ : Unique (x₁ ∷ map proj₁ _)
          uls₂ = g₂ (map proj₁ _) (λ x₃ → dsj (here refl , x₃)) ∷ uls

¬bf : ∀ {x : Cmd} {x₁} zs → x ∉ zs → ¬ (x before x₁ ∈ (zs ∷ʳ x))
{- need to prove ys is empty. then x₁ cannot be in empty list -}
¬bf {x} [] x∉zs ([] , ys , ≡₁ , x₁∈ys) with ++-identityˡ (x ∷ [])
... | a with ∷-injectiveʳ ≡₁
... | refl = contradiction x₁∈ys (λ ())
¬bf {x} [] x∉zs (x₂ ∷ xs , ys , ≡₁ , x₁∈ys) with ++-identityˡ (x ∷ [])
... | _ with ∷-injectiveʳ ≡₁
... | ≡₂ = contradiction (subst (λ x₃ → _ ∈ x₃) (sym ≡₂) (∈-++⁺ʳ xs (there x₁∈ys))) (λ ())
¬bf (x₂ ∷ zs) x∉zs ([] , ys , ≡₁ , x₁∈ys) = contradiction (here (sym (∷-injectiveˡ ≡₁))) x∉zs
¬bf (x₂ ∷ zs) x∉zs (x₃ ∷ xs , ys , ≡₁ , x₁∈ys) with ¬bf zs λ x₄ → x∉zs (there x₄)
... | ¬bf₁ = ¬bf₁ (xs , ys , ∷-injectiveʳ ≡₁ , x₁∈ys)

{- prove the writes of x are disjoint from the reads of x₁ using evidence of no speculative hazard
-}
disjoint3 : ∀ s x₁ zs x ls → x ∈ map proj₁ ls → x₁ ∈ zs → x ∉ zs → ¬ Hazard s x₁ (zs ∷ʳ x) ls → Disjoint (cmdWrote ls x) (cmdReadNames x₁ s)
disjoint3 s x₁ zs x ls x∈ls x₁∈zs x∉zs ¬hz x₄ = ¬hz (Speculative x x₁ bf (∈-++⁺ˡ x₁∈zs) (¬bf zs x∉zs) (∈-cmdRead∷l (x₁ , _) ls (proj₂ x₄)) (∈-cmdWrote∷ (x₁ , _) x ls (proj₁ x₄) λ x₁≡x → x∉zs (subst (λ x₅ → x₅ ∈ zs) x₁≡x x₁∈zs)))
  where bf : x₁ before x ∈ (x₁ ∷ map proj₁ ls)
        bf = [] , map proj₁ ls , refl , x∈ls


hf=>disjoint2 : ∀ s ls ys zs x → ys ⊆ zs → x ∉ zs → x ∈ map proj₁ ls → HazardFree s ys (zs ∷ʳ x) ls → Disjoint (cmdWrote ls x) (buildReadNames s ys)
hf=>disjoint2 s ls [] zs x ys⊆zs x∉zs x∈ls hf = g₁
  where g₁ : Disjoint (cmdWrote ls x) (buildReadNames s [])
        g₁ ()
hf=>disjoint2 s ls (x₁ ∷ ys) zs x ys⊆zs x∉zs x∈ls (¬hz ∷ hf) with hf=>disjoint2 (run x₁ s) (save s x₁ ls) ys zs x (λ x₃ → ys⊆zs (there x₃)) x∉zs (there x∈ls) hf
... | dsj₁ = g₁
  where g₁ : Disjoint (cmdWrote ls x) (buildReadNames s (x₁ ∷ ys))
        g₁ (∈₁ , ∈₂) with ∈-++⁻ (cmdReadNames x₁ s) ∈₂
        ... | inj₁ ∈cmd = disjoint3 s x₁ zs x ls x∈ls (ys⊆zs (here refl)) x∉zs ¬hz (∈₁ , ∈cmd)
        ... | inj₂ ∈build = dsj₁ ((∈-cmdWrote∷ (x₁ , _) x ls ∈₁ λ x₁≡x → x∉zs (ys⊆zs (here (sym x₁≡x)))) , ∈build)

hf=>disjoint1 : ∀ s x ys zs ls → ys ⊆ zs → x ∉ zs → HazardFree s (x ∷ ys) (zs ∷ʳ x) ls → Disjoint (cmdWriteNames x s) (buildReadNames (run x s) ys)
hf=>disjoint1 s x ys zs ls ys⊆zs x∉zs (x₁ ∷ hf) with hf=>disjoint2 (run x s) (save s x ls) ys zs x ys⊆zs x∉zs (here refl) hf
... | dsj = λ x₁ → dsj (∈-cmdWrote∷l (x , _) ls (proj₁ x₁) , (proj₂ x₁))

hf=>disjoint : ∀ s x xs ys zs ls → ys ⊆ zs → x ∉ zs → HazardFree s (xs ++ x ∷ ys) (zs ∷ʳ x) ls → Disjoint (cmdWriteNames x (script xs s)) (buildReadNames (run x (script xs s)) ys)
hf=>disjoint s x [] ys zs ls ys⊆zs x∉zs hf = hf=>disjoint1 s x ys zs ls ys⊆zs x∉zs hf
hf=>disjoint s x (x₁ ∷ xs) ys zs ls ys⊆zs x∉zs (x₂ ∷ hf)
  = hf=>disjoint (run x₁ s) x xs ys zs _ ys⊆zs x∉zs hf

hf=>disjointWW3 : ∀ s x₁ zs x ls → x ∈ map proj₁ ls → x₁ ∈ zs → x ∉ zs → ¬ Hazard s x₁ (zs ∷ʳ x) ls → Disjoint (filesWrote ls) (cmdWriteNames x₁ s)
hf=>disjointWW3 s x₁ zs x ls x∈ls x₁∈zs x∉zs ¬hz x₄ = ¬hz (WriteWrite (proj₂ x₄) (proj₁ x₄))

hf=>disjointWW2 : ∀ s ls ys zs x → ys ⊆ zs → x ∉ zs → x ∈ map proj₁ ls → HazardFree s ys (zs ∷ʳ x) ls → Disjoint (filesWrote ls) (buildWriteNames s ys)
hf=>disjointWW2 s ls [] zs x ys⊆zs x∉zs x∈ls hf = g₁
  where g₁ : Disjoint (filesWrote ls) (buildWriteNames s [])
        g₁ ()
hf=>disjointWW2 s ls (x₁ ∷ ys) zs x ys⊆zs x∉zs x∈ls (x₂ ∷ hf) with hf=>disjointWW2 (run x₁ s) (save s x₁ ls) ys zs x (λ x₃ → ys⊆zs (there x₃)) x∉zs (there x∈ls) hf
... | dsj = g₁
  where g₁ : Disjoint (filesWrote ls) (buildWriteNames s (x₁ ∷ ys))
        g₁ (∈₁ , ∈₂) with ∈-++⁻ (cmdWriteNames x₁ s) ∈₂
        ... | inj₁ ∈cmd = hf=>disjointWW3 s x₁ zs x ls x∈ls (ys⊆zs (here refl)) x∉zs x₂ (∈₁ , ∈cmd)
        ... | inj₂ ∈build = dsj (∈-++⁺ʳ _ ∈₁ , ∈build)

hf=>disjointWW1 : ∀ s x ys zs ls → ys ⊆ zs → x ∉ zs → HazardFree s (x ∷ ys) (zs ∷ʳ x) ls → Disjoint (cmdWriteNames x s) (buildWriteNames (run x s) ys)
hf=>disjointWW1 s x ys zs ls ys⊆zs x∉zs (x₁ ∷ hf) with hf=>disjointWW2 (run _ s) (save s x ls) ys zs x ys⊆zs x∉zs (here refl) hf
... | dsj = λ x₂ → dsj (∈-++⁺ˡ (proj₁ x₂) , (proj₂ x₂))

hf=>disjointWW : ∀ s x xs ys zs ls → ys ⊆ zs → x ∉ zs → HazardFree s (xs ++ x ∷ ys) (zs ∷ʳ x) ls → Disjoint (cmdWriteNames x (script xs s)) (buildWriteNames (run x (script xs s)) ys)
hf=>disjointWW s x [] ys zs ls ys⊆zs x∉zs hf
  = hf=>disjointWW1 s x ys zs ls ys⊆zs x∉zs hf
hf=>disjointWW s x (x₁ ∷ xs) ys zs ls ys⊆zs x∉zs (x₂ ∷ hf)
  = hf=>disjointWW (run x₁ s) x xs ys zs _ ys⊆zs x∉zs hf

hf=>disjointRW3 : ∀ s x₁ zs x ls → x ∈ map proj₁ ls → x₁ ∈ zs → x ∉ zs → ¬ Hazard s x₁ (zs ∷ʳ x) ls → Disjoint (filesRead ls) (cmdWriteNames x₁ s)
hf=>disjointRW3 s x₁ zs x ls x∈ls x₁∈zs x∉zs ¬hz x₄ = ¬hz (ReadWrite (proj₂ x₄) (proj₁ x₄))

hf=>disjointRW2 : ∀ s ls ys zs x → ys ⊆ zs → x ∉ zs → x ∈ map proj₁ ls → HazardFree s ys (zs ∷ʳ x) ls → Disjoint (filesRead ls) (buildWriteNames s ys)
hf=>disjointRW2 s ls [] zs x ys⊆zs x∉zs x∈ls hf = g₁
  where g₁ : Disjoint (filesRead ls) (buildWriteNames s [])
        g₁ ()
hf=>disjointRW2 s ls (x₁ ∷ ys) zs x ys⊆zs x∉zs x∈ls (x₂ ∷ hf) with hf=>disjointRW2 (run x₁ s) (save s x₁ ls) ys zs x (λ x₃ → ys⊆zs (there x₃)) x∉zs (there x∈ls) hf
... | dsj = g₁
  where g₁ : Disjoint (filesRead ls) (buildWriteNames s (x₁ ∷ ys))
        g₁ (∈₁ , ∈₂) with ∈-++⁻ (cmdWriteNames x₁ s) ∈₂
        ... | inj₁ ∈cmd = hf=>disjointRW3 s x₁ zs x ls x∈ls (ys⊆zs (here refl)) x∉zs x₂ (∈₁ , ∈cmd)
        ... | inj₂ ∈build = dsj (∈-++⁺ʳ _ ∈₁ , ∈build)

hf=>disjointRW1 : ∀ s x ys zs ls → ys ⊆ zs → x ∉ zs → HazardFree s (x ∷ ys) (zs ∷ʳ x) ls → Disjoint (cmdReadNames x s) (buildWriteNames (run x s) ys)
hf=>disjointRW1 s x ys zs ls ys⊆zs x∉zs (x₁ ∷ hf) with hf=>disjointRW2 (run _ s) (save s x ls) ys zs x ys⊆zs x∉zs (here refl) hf
... | dsj = λ x₂ → dsj (∈-++⁺ˡ (proj₁ x₂) , (proj₂ x₂))

hf=>disjointRW : ∀ s x xs ys zs ls → ys ⊆ zs → x ∉ zs → HazardFree s (xs ++ x ∷ ys) (zs ∷ʳ x) ls → Disjoint (cmdReadNames x (script xs s)) (buildWriteNames (run x (script xs s)) ys)
hf=>disjointRW s x [] ys zs ls ys⊆zs x∉zs hf
  = hf=>disjointRW1 s x ys zs ls ys⊆zs x∉zs hf
hf=>disjointRW s x (x₁ ∷ xs) ys zs ls ys⊆zs x∉zs (x₂ ∷ hf)
  = hf=>disjointRW (run x₁ s) x xs ys zs _ ys⊆zs x∉zs hf

hf=>disjointWR3 : ∀ s x₁ zs x ls → x ∈ map proj₁ ls → x₁ ∈ zs → x ∉ zs → ¬ Hazard s x₁ (zs ∷ʳ x) ls → Disjoint (cmdWrote ls x) (cmdReadNames x₁ s)
hf=>disjointWR3 s x₁ zs x ls x∈ls x₁∈zs x∉zs ¬hz x₄ = ¬hz (Speculative x x₁ bf (∈-++⁺ˡ x₁∈zs) (¬bf zs x∉zs) (∈-cmdRead∷l (x₁ , (cmdReadNames x₁ s) , _) ls (proj₂ x₄)) (∈-cmdWrote∷ (x₁ , _ , _) x ls (proj₁ x₄) λ x₂ → x∉zs (subst (λ x₃ → x₃ ∈ zs) x₂ x₁∈zs)))
  where bf : x₁ before x ∈ (x₁ ∷ cmdsRun ls)
        bf = [] , cmdsRun ls , refl , x∈ls

hf=>disjointWR2 : ∀ s ls ys zs x → ys ⊆ zs → x ∉ zs → x ∈ map proj₁ ls → HazardFree s ys (zs ∷ʳ x) ls → Disjoint (cmdWrote ls x) (buildReadNames s ys)
hf=>disjointWR2 s ls [] zs x ys⊆zs x∉zs x∈ls hf = g₁
  where g₁ : Disjoint (cmdWrote ls x) (buildReadNames s [])
        g₁ ()
hf=>disjointWR2 s ls (x₁ ∷ ys) zs x ys⊆zs x∉zs x∈ls (x₂ ∷ hf) with hf=>disjointWR2 (run x₁ s) (save s x₁ ls) ys zs x (λ x₃ → ys⊆zs (there x₃)) x∉zs (there x∈ls) hf
... | dsj = g₁
  where g₁ : Disjoint (cmdWrote ls x) (buildReadNames s (x₁ ∷ ys))
        g₁ (∈₁ , ∈₂) with ∈-++⁻ (cmdReadNames x₁ s) ∈₂
        ... | inj₁ ∈cmd = hf=>disjointWR3 s x₁ zs x ls x∈ls (ys⊆zs (here refl)) x∉zs x₂ (∈₁ , ∈cmd)
        ... | inj₂ ∈build = dsj (∈-cmdWrote∷ (x₁ , _ , _) x ls ∈₁ (λ x₃ → x∉zs (subst (λ x₄ → x₄ ∈ zs) x₃ (ys⊆zs (here refl)))) , ∈build)

hf=>disjointWR1 : ∀ s x ys zs ls → ys ⊆ zs → x ∉ zs → HazardFree s (x ∷ ys) (zs ∷ʳ x) ls → Disjoint (cmdWriteNames x s) (buildReadNames (run x s) ys)
hf=>disjointWR1 s x ys zs ls ys⊆zs x∉zs (x₁ ∷ hf) with hf=>disjointWR2 (run _ s) (save s x ls) ys zs x ys⊆zs x∉zs (here refl) hf
... | dsj = λ x₂ → dsj (∈-cmdWrote∷l (x , _ , (cmdWriteNames x s)) ls (proj₁ x₂) , proj₂ x₂)

hf=>disjointWR : ∀ s x xs ys zs ls → ys ⊆ zs → x ∉ zs → HazardFree s (xs ++ x ∷ ys) (zs ∷ʳ x) ls → Disjoint (cmdWriteNames x (script xs s)) (buildReadNames (run x (script xs s)) ys)
hf=>disjointWR s x [] ys zs ls ys⊆zs x∉zs hf = hf=>disjointWR1 s x ys zs ls ys⊆zs x∉zs hf
hf=>disjointWR s x (x₁ ∷ xs) ys zs ls ys⊆zs x∉zs (x₂ ∷ hf)
  = hf=>disjointWR (run x₁ s) x xs ys zs _ ys⊆zs x∉zs hf

--------------------------------------- preserves hazards --------------------------------------------------------
script-rec : ∀ (b : Build) s ls → FileInfo
script-rec [] s ls = ls
script-rec (x ∷ b) s ls = script-rec b (run x s) (save s x ls)

¬Speculative : Build → FileInfo → Set
¬Speculative xs ls = ∀ x₁ x₂ → x₂ before x₁ ∈ cmdsRun ls → ¬ (x₁ before x₂ ∈ xs) → Disjoint (cmdWrote ls x₁) (cmdRead ls x₂)

hf-+∷ʳ-left : ∀ {s} {ls} {ys} xs x → ¬ (Hazard (script xs s) x ys (script-rec xs s ls)) → HazardFree s xs ys ls → HazardFree s (xs ∷ʳ x) ys ls
hf-+∷ʳ-left [] x ¬hz [] = (¬hz ∷ [])
hf-+∷ʳ-left (x₁ ∷ xs) x ¬hz₁ (¬hz ∷ hf) = ¬hz ∷ (hf-+∷ʳ-left xs x ¬hz₁ hf)

hf--∷ʳ-left : ∀ {s} {ls} {ys} xs x → HazardFree s (xs ∷ʳ x) ys ls → (HazardFree s xs ys ls × ¬ (Hazard (script xs s) x ys (script-rec xs s ls)))
hf--∷ʳ-left [] x (¬hz ∷ []) = ([] , ¬hz) 
hf--∷ʳ-left (x₁ ∷ xs) x (¬hz ∷ hf) = map₁ (¬hz ∷_) (hf--∷ʳ-left xs x hf)


hf-remove-extras : ∀ {s} {ls} xs ys → HazardFree s (reverse xs) ys ls → ∃[ zs ](zs ⊆ ys × files (script-rec zs s ls) ⊆ files (script-rec (reverse xs) s ls) × HazardFree s zs ys ls)
hf-remove-extras [] ys hf = [] , (λ ()) , (λ x → x) , []
hf-remove-extras {s} {ls} (x ∷ xs) ys hf with x ∈? ys
... | no x∉ys with hf-remove-extras xs ys hf₁
  where hf₁ : HazardFree s (reverse xs) ys ls
        hf₁ = proj₁ (hf--∷ʳ-left (reverse xs) x (subst (λ x₁ → HazardFree s x₁ ys ls)
                                                (unfold-reverse x xs) hf))
... | (zs , a1 , a2 , hf₁) = (zs , a1 , (λ x₁ → {!!}) , hf₁)
hf-remove-extras {s} {ls} (x ∷ xs) ys hf | yes x∈ys with hf-remove-extras xs ys hf₁
    where hf₁ : HazardFree s (reverse xs) ys ls
          hf₁ = proj₁ (hf--∷ʳ-left (reverse xs) x (subst (λ x₁ → HazardFree s x₁ ys ls)
                                                (unfold-reverse x xs) hf))
... | (zs , zs⊆ys , _ , hf₁) = zs ++ (x ∷ []) , zs++x∷[]⊆ys , {!!} , (hf-+∷ʳ-left zs x ¬hz hf₁)
  where ¬hz₁ : ¬ (Hazard (script (reverse xs) s) x ys (script-rec (reverse xs) s ls))
        ¬hz₁ = proj₂ (hf--∷ʳ-left (reverse xs) x (subst (λ x₁ → HazardFree s x₁ ys ls)
                                                (unfold-reverse x xs) hf))
        ≡₁ : proj₁ (oracle x) (script (reverse xs) s) ≡ proj₁ (oracle x) (script zs s)
        ≡₁ = proj₂ (oracle x) (script (reverse xs) s) (script zs s)
             λ f₁ x₁ → {!!}
        ¬hz : ¬ (Hazard (script zs s) x ys (script-rec zs s ls))
        ¬hz (ReadWrite x x₁) = ¬hz₁ (ReadWrite {!!} {!!})
        ¬hz (WriteWrite x x₁) = ¬hz₁ (WriteWrite {!!} {!!})
        ¬hz (Speculative x₁ x₂ x x₃ x₄ x₅ x₆)
          = ¬hz₁ (Speculative {!!} {!!} {!!} {!!} {!!} {!!} {!!})
        zs++x∷[]⊆ys : zs ++ x ∷ [] ⊆ ys
        zs++x∷[]⊆ys x₁∈zs++[x] with ∈-++⁻ zs x₁∈zs++[x]
        ... | inj₁ x₁∈zs = zs⊆ys x₁∈zs
        ... | inj₂ (here x₁≡x) = subst (λ x₂ → x₂ ∈ ys) (sym x₁≡x) x∈ys


{- Need to prove x does same thing when run in both builds. 
   I'm extremely not sure how to prove this in the current state. 
   What if I reduce the problem? and remove all of the extra commands from the build run?
-}
≡-result : ∀ {s} as bs cs ds x → HazardFree s (as ++ x ∷ bs) (cs ++ x ∷ (reverse ds)) [] → proj₁ (oracle x) (script as s) ≡ proj₁ (oracle x) (script cs s)
≡-result {s} as bs cs [] x hf = {!!}
≡-result {s} as bs cs (x₁ ∷ ds) x hf = {!!}

{- Either our hazardfree evidence has the same hazard, or there is a speculative hazard?
  1. we should know but haven't proven that for all cmds in both lists. they will have the same result....
  2. we should know there isn't a speculative hazard. so we should be able to contradict that away
  3. since there is a writewrite/readwrite hazard, we know there is a command x₁ that read/wrote to the file. 
  4. if x₁ is before x in ys, then we produce a contradiction with that ¬ hazard evidence for x.
  5. if x₁ is after x in ys, then we produce a contradiction using the ¬ hazard evidence for x₁; because that is a speculative hazard.

  of course there are more details to figuring these things out.
-}
hazard-contradiction : ∀ {s₁} {s} {ls} x zs ys → x ∈ ys → Hazard s₁ x zs ls → HazardFree s ys zs [] → ⊥ 
hazard-contradiction x zs ys x∈ys (ReadWrite x₁ x₂) hf = {!!}
hazard-contradiction x zs ys x∈ys (WriteWrite x₁ x₂) hf = {!!}

hazard-contradiction x zs ys x∈ys (Speculative x₁ x₂ x₃ x₄ x₅ x₆ x₇) hf = {!!}


preserves-hazardFree : ∀ {s} {s₁} {ls} xs ys zs → xs ⊆ zs → zs ⊆ ys → HazardFree s ys zs [] → HazardFree s₁ xs zs ls
preserves-hazardFree [] ys zs xs⊆zs zs⊆ys hf = []
preserves-hazardFree (x ∷ xs) ys zs xs⊆zs zs⊆ys hf
  = (λ x₁ → {!!}) ∷ (preserves-hazardFree xs ys zs (λ x₁ → xs⊆zs (there x₁)) zs⊆ys hf)

preserves-hazards : ∀ {s} xs ys → xs ⊆ ys → ¬ HazardFree s xs xs [] → ¬ HazardFree s ys xs []
preserves-hazards xs ys xs⊆ys hz hf = hz {!!}


hazardFree-self : ∀ {s} {ls} xs ys → HazardFree s xs ys ls → HazardFree s xs xs ls
hazardFree-self xs ys hf = {!!}
  where g₁ : ∀ {s} {ls} xs ys zs → HazardFree s xs ys ls → HazardFree s xs zs ls
        g₁ [] ys zs [] = []
        g₁ {s} {ls} (x ∷ xs) ys zs (¬hz ∷ hf) = ¬hz₂ ∷ (g₁ xs ys zs hf)
          where ¬hz₂ : ¬ (Hazard s x zs ls)
                ¬hz₂ (ReadWrite x x₁) = ¬hz (ReadWrite x x₁)
                ¬hz₂ (WriteWrite x x₁) = ¬hz (WriteWrite x x₁)
                ¬hz₂ (Speculative x₁ x₂ x x₃ x₄ x₅ x₆) = {!!}

{-# OPTIONS --allow-unsolved-metas #-}
open import Functional.State as St using (F ; run-≡ ; run ; System ; Cmd)

module Functional.Script.Hazard.Properties (oracle : F) where
open import Functional.Script.Exec (oracle) using (exec ; reads ; Creads)
open import Functional.Build using (Unique-> ; Build)
open import Common.List.Properties using (_before_en_)
open import Agda.Builtin.Equality
open import Functional.File using (FileName)
open import Functional.Script.Hazard.Base (oracle) using (HazardFree ; [] ; :: ; cmdReads ; cmdWrites ; files ; cmdsRun ; cmdWrote ; FileInfo ; save ; filesRead ; ¬SpeculativeHazard ; ∈-files-++ ; ∈-cmdRead++mid ; ∈-cmdWrote++mid ; ∈-cmdWrote∷ ; ∈-cmdRead∷l ; lemma2 ; cmdWrote∷-≡)
open import Data.List as L using (_∷_ ; _++_ ; map ; foldr ; List ; foldl ; _∷ʳ_ ; [] ; reverse ; [_])
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; _×_ ; Σ-syntax ; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (subst ; subst₂ ; cong ; sym ; trans ; cong₂)
open import Function using (_∘_)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Membership.Propositional using (_∈_ ; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-∃++)
open import Data.String using (String)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List.Properties using (map-++-commute ; ++-assoc ; reverse-involutive ; ∷-injectiveˡ ; ∷-injectiveʳ ; reverse-++-commute ; unfold-reverse)
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

{- what does memoize do about duplicates? 

  The following property is nice: build is idempotent

    
  
  #1 write #2 

  #2 write ()

  we shouldn't care about forward builds with duplicate commands; because builds can't be idempotent 

-}

-- need some more evidence. need to know x₂ ¬≡ x
¬bf-∷ʳ : ∀ (x : Cmd) x₁ {x₂} b₁ → ¬ x₂ ≡ x → ¬ x₁ before x₂ en b₁ → ¬ x₁ before x₂ en (b₁ ∷ʳ x)
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

¬sh-∷ʳ : ∀ b₁ x {ls} → Unique (b₁ ∷ʳ x) → ¬SpeculativeHazard (b₁ ∷ʳ x) ls → ¬SpeculativeHazard b₁ ls
¬sh-∷ʳ b₁ x u ¬sh = λ x₁ x₂ x₃ x₄ x₅ x₆ → ¬sh x₁ x₂ x₃ (∈-++⁺ˡ x₄) (¬bf-∷ʳ x x₁ b₁ (unique→¬≡ b₁ x₂ x₄ u) x₅) x₆

hf-∷ʳ-l : ∀ {s} b₁ {b₂} {x} {ls} → HazardFree s (b₁ ∷ʳ x) b₂ ls → HazardFree s b₁ b₂ ls
hf-∷ʳ-l List.[] hf = []
hf-∷ʳ-l (x ∷ b₁) (:: _ _ .x .(b₁ ++ _ ∷ List.[]) b₂ x₁ x₂ hf)
  = :: _ _ x b₁ b₂ x₁ x₂ (hf-∷ʳ-l b₁ hf)
hf-∷ʳ-r : ∀ {s} b₁ b₂ {x} {ls} → Unique (b₂ ∷ʳ x) → HazardFree s b₁ (b₂ ∷ʳ x) ls → HazardFree s b₁ b₂ ls
hf-∷ʳ-r [] b₂ u hf = []
hf-∷ʳ-r (x ∷ b₁) b₂ u (:: _ _ .x .b₁ .(b₂ ++ _ ∷ []) x₁ x₂ hf)
  = :: _ _ x b₁ b₂ (¬sh-∷ʳ b₂ _ u x₁) x₂ (hf-∷ʳ-r b₁ b₂ u hf)

disjoint-drop-mid : ∀ ls xs ys zs → Disjoint ls (files (xs ++ ys ++ zs)) → Disjoint ls (files (xs ++ zs))
disjoint-drop-mid ls xs ys zs dsj = λ x → dsj (proj₁ x , ∈-files-++ xs ys zs (proj₂ x))


before-add-mid : ∀ x₂ x₁ (xs : Build) ys zs → x₂ before x₁ en (xs ++ zs) → x₂ before x₁ en (xs ++ ys ++ zs)
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


¬sh-drop-mid : ∀ b xs ys zs → Unique (map proj₁ (xs ++ ys ++ zs)) → ¬SpeculativeHazard b (xs ++ ys ++ zs) → ¬SpeculativeHazard b (xs ++ zs)
¬sh-drop-mid b xs ys zs u ¬sh x₁ x₂ bf x₃ x₄ x₅ = ¬sh x₁ x₂ bf₁ x₃ x₄ (∈-cmdRead++mid x₂ xs ys zs u (proj₁ x₅) , ∈-cmdWrote++mid x₁ xs ys zs u (proj₂ x₅))
  where bf₁ : x₂ before x₁ en map proj₁ (xs ++ ys ++ zs)
        bf₁ with before-add-mid x₂ x₁ (map proj₁ xs) (map proj₁ ys) (map proj₁ zs) (subst (λ ls → x₂ before x₁ en ls) (map-++-commute proj₁ xs zs) bf)
        ... | bf₂ = subst (λ ls → x₂ before x₁ en ls) (sym (trans (map-++-commute proj₁ xs (ys ++ zs)) (cong (map proj₁ xs ++_) (map-++-commute proj₁ ys zs)))) bf₂

-- there is a copy of this elsewhere so maybe organize this better.
g₂ : ∀ {x : Cmd} xs → x ∉ xs → All (λ y → ¬ x ≡ y) xs
g₂ [] x∉xs = All.[]
g₂ (x ∷ xs) x∉xs = (λ x₃ → x∉xs (here x₃)) All.∷ (g₂ xs λ x₃ → x∉xs (there x₃))

hf-still : ∀ {s₁} {s} b₁ {b₂} xs ys zs → (∀ f₁ → f₁ ∈ reads s₁ b₁ → s₁ f₁ ≡ s f₁) → Unique b₁ → Unique (map proj₁ (xs ++ ys ++ zs)) → Disjoint b₁ (map proj₁ (xs ++ ys ++ zs)) → HazardFree s₁ b₁ b₂ (xs ++ ys ++ zs) → HazardFree s b₁ b₂ (xs ++ zs)
hf-still [] xs ys zs ∀₁ ub₁ u dsj hf = []
hf-still {s₁} {s} (x ∷ b₁) xs ys zs ∀₁ (px ∷ ub₁) u dsj (:: _ .(xs ++ ys ++ zs) .x .b₁ _ ¬sh x₂ hf)
  = :: _ (xs ++ zs) x b₁ _ ¬sh₂ (subst (λ x₃ → Disjoint x₃ (files (xs ++ zs))) ≡₁ (disjoint-drop-mid (cmdWrites _ x) xs ys zs x₂))
         (hf-still b₁ (save x (cmdReads s x) (cmdWrites s x) xs) ys zs ∀₂ ub₁ u₂ dsj₁ hf₂) 
    where dsj₁ : Disjoint b₁ (x ∷ map proj₁ (xs ++ ys ++ zs))
          dsj₁ = λ x₁ → dsj (there (proj₁ x₁) , tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
          ≡₀ : proj₁ (oracle x) s₁ ≡ proj₁ (oracle x) s
          ≡₀ = (proj₂ (oracle x) s₁ s λ f₁ x₃ → ∀₁ f₁ (∈-++⁺ˡ x₃))
          ≡₁ : cmdWrites s₁ x ≡ cmdWrites s x
          ≡₁ = cong (map proj₁ ∘ proj₂) ≡₀
          ≡₂ : cmdReads s₁ x ≡ cmdReads s x
          ≡₂ = cong (map proj₁ ∘ proj₁) ≡₀
          hf₂ : HazardFree (run oracle x s₁) b₁ _ ((x , cmdReads s x , cmdWrites s x) ∷ xs ++ ys ++ zs)
          hf₂ = subst (λ x₃ → HazardFree (run oracle x s₁) b₁ _ (x₃ ∷ xs ++ ys ++ zs))
                      (cong (x ,_) (cong₂ _,_ ≡₂ ≡₁)) hf
          ∀₂ : ∀ f₁ → f₁ ∈ reads (run oracle x s₁) b₁ → run oracle x s₁ f₁ ≡ run oracle x s f₁
          ∀₂ f₁ f₁∈ with ∀₁ f₁ (∈-++⁺ʳ (Creads s₁ x) f₁∈)
          ... | s₁f₁≡sf₁ = St.lemma2 {oracle} x f₁ ≡₀ s₁f₁≡sf₁
          u₂ : Unique (x ∷ (map proj₁ (xs ++ ys ++ zs)))
          u₂ = (g₂ (map proj₁ (xs ++ ys ++ zs)) λ x₁ → dsj (here refl , x₁)) ∷ u
          ¬sh₂ : ¬SpeculativeHazard _ (save x (cmdReads s x) (cmdWrites s x) (xs ++ zs))
          ¬sh₂ = ¬sh-drop-mid _ ((x , (cmdReads s x) , (cmdWrites s x)) ∷ xs) ys zs u₂
                              (subst₂ (λ x₁ x₃ → ¬SpeculativeHazard _ (save x x₁ x₃ (xs ++ ys ++ zs))) ≡₂ ≡₁ ¬sh)

lemma3 : ∀ {s} {x} {ls} → Disjoint (cmdWrites s x) ls → (∀ f₁ → f₁ ∈ ls → run oracle x s f₁ ≡ s f₁)
lemma3 {s} {x} dsj f₁ f₁∈ls with f₁ ∈? cmdWrites s x
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
lemma4 : ∀ {s} {x} ys {b₁} {ls} → x ∉ ys → ys ⊆ (b₁ ∷ʳ x) → Unique (b₁ ∷ʳ x) → HazardFree s ys (b₁ ∷ʳ x) ls → Disjoint (cmdWrote ls x) (reads s ys)
lemma4 [] x∉ys ⊆₁ u [] = λ ()
lemma4 {s} {x} (x₃ ∷ b₂) {b₁} x∉ys ⊆₁ u (:: _ _ .x₃ .b₂ .(_ ++ _ ∷ []) ¬sh x₂ hf) x₄ with ∈-++⁻ (Creads s x₃) (proj₂ x₄)
... | inj₁ v∈₁ = contradiction (∈-cmdRead∷l x₃i _ v∈₁ , ∈-cmdWrote∷ x₃i x _ (proj₁ x₄) (g₄ (here refl) x∉ys)) (¬sh x x₃ ([] , map proj₁ _ , refl , lemma2 x _ (proj₁ x₄)) (⊆₁ (here refl)) ¬bf)
  where x₃i : (Cmd × List FileName × List FileName)
        x₃i = (x₃ , (cmdReads s x₃) , (cmdWrites s x₃))
        ¬bf : ¬ x before x₃ en (_ ∷ʳ x)
        ¬bf (xs , ys , b₁∷ʳx≡xs++x∷ys , x₃∈ys) = contradiction refl (unique→¬≡ b₁ x (reverse⁻ (g₃ (reverse ys) ≡₂ (reverse⁺ x₃∈ys))) u)
          where ≡₂ : x ∷ reverse b₁ ≡ reverse ys ∷ʳ x ++ reverse xs
                ≡₂ = trans (sym (reverse-++-commute b₁ [ x ]))
                           (trans (cong reverse b₁∷ʳx≡xs++x∷ys)
                                  (trans (reverse-++-commute xs (x ∷ ys))
                                         (cong (_++ reverse xs) (unfold-reverse x ys))))
... | inj₂ v∈₂ = (lemma4 b₂ (λ x₁ → x∉ys (there x₁)) (λ x₁ → ⊆₁ (there x₁)) u hf) (∈-cmdWrote∷ x₃i x _ (proj₁ x₄) (g₄ (here refl) x∉ys) , v∈₂)
  where x₃i : (Cmd × List FileName × List FileName)
        x₃i = (x₃ , (cmdReads s x₃) , (cmdWrites s x₃))

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
hf-drop-mid {s} List.[] ys b₁ {x} ⊆₁ (px₁ ∷ u₁) u uls dsj (:: .s _ _ .ys _ ¬sh x₂ hf) with hf-still ys [] [ (x , (cmdReads s x) , (cmdWrites s x)) ] _ ∀₁ u₁ uls₂ dsj₁ hf
  where dsj₁ : Disjoint ys (x ∷ map proj₁ _)
        dsj₁ = λ x₁ → dsj (there (proj₁ x₁) , tail (λ v≡x → lookup px₁ (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
        uls₂ : Unique (x ∷ map proj₁ _)
        uls₂ = g₂ (map proj₁ _) (λ x₁ → dsj (here refl , x₁)) ∷ uls
        ∀₁ : ∀ f₁ → f₁ ∈ reads (run oracle x s) ys → run oracle x s f₁ ≡ s f₁
        ∀₁ = lemma3 (subst (λ x₁ → Disjoint x₁ (reads (run oracle x s) ys)) (cmdWrote∷-≡ (x , (cmdReads s x) , (cmdWrites s x)) _) (lemma4 ys (g₅ x ys px₁) (λ x₁ → ⊆₁ (there x₁)) u hf))
... | hf₂ = hf-∷ʳ-r ys b₁ u hf₂
hf-drop-mid (x₁ ∷ xs) ys b₁ {x} ⊆₁ (px₁ ∷ u₁) u uls dsj (:: _ _ .x₁ .(xs ++ _ ∷ ys) _ ¬sh x₂ hf)
  = :: _ _ x₁ (xs ++ ys) _ (¬sh-∷ʳ b₁ x u ¬sh) x₂ (hf-drop-mid xs ys b₁ (λ x₃ → ⊆₁ (there x₃)) u₁ u uls₂ dsj₁ hf)
    where dsj₁ : Disjoint (xs ++ x ∷ ys) (x₁ ∷ map proj₁ _)
          dsj₁ = λ x₃ → dsj (there (proj₁ x₃) , tail (λ v≡x₁ → lookup px₁ (proj₁ x₃) (sym v≡x₁)) (proj₂ x₃))
          uls₂ : Unique (x₁ ∷ map proj₁ _)
          uls₂ = g₂ (map proj₁ _) (λ x₃ → dsj (here refl , x₃)) ∷ uls

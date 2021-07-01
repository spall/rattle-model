
module Common.List.Properties where

open import Agda.Builtin.Equality

open import Data.List using (List ; _++_ ; [_] ; _∷ʳ_ ; [] ; _∷_ ; reverse)
open import Data.List.Properties using (++-identityʳ ; unfold-reverse ; ++-assoc ; ∷-injective ; ∷-injectiveʳ)
open import Data.List.Membership.Propositional using (_∈_ ; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-insert ; ∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-∃++)
open import Relation.Binary.PropositionalEquality using (subst ; sym ; cong ; trans ; cong₂)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (drop-mid)
open import Data.List.Relation.Unary.Any using (there ; here)
open import Data.Product using (∃-syntax ; _,_ ; _×_)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)

open import Data.List.Categorical using (monad)
open import Category.Monad using (RawMonad)
open import Level using (Level)

private
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})

  variable
    ℓ : Level
    A : Set ℓ

l10 : ∀ (v : A) xs ys → (xs ++ ys) ∷ʳ v ≡ xs ++ ys ∷ʳ v
l10 v [] ys = refl
l10 v (x ∷ xs) ys = cong (x ∷_) (l10 v xs ys)


_before_en_ : A -> A -> List A -> Set _ -- why the _ ?
v before w en xs = ∃[ ys ](∃[ zs ](xs ≡ ys ++ [ v ] ++ zs × w ∈ zs))

-- properties about _before_en_ --

before-∷ʳ⁺ : ∀ (v w x : A) xs → v before w en xs -> v before w en (xs ∷ʳ x)
before-∷ʳ⁺ v w x xs (as , bs , xs≡as++v∷bs , w∈bs)
  = as , bs ∷ʳ x , trans (cong (_∷ʳ x) xs≡as++v∷bs) (l10 x as (v ∷ bs)) , (∈-++⁺ˡ w∈bs)

-- more of a constructor
∈→before-∷ʳ : ∀ (v w : A) xs -> v ∈ xs -> v before w en (xs ∷ʳ w)
∈→before-∷ʳ v w xs v∈xs with ∈-∃++ v∈xs
... | ys , zs , xs≡ys++v∷zs
  = ys , zs ∷ʳ w , trans (cong (_∷ʳ w) xs≡ys++v∷zs) (l10 w ys (v ∷ zs)) , ∈-++⁺ʳ zs (here refl)

-- end of properties about _before_en_ --

∈-resp-≡ : ∀ (v : A) xs ys → xs ≡ ys -> v ∈ xs -> v ∈ ys
∈-resp-≡ v xs ys xs≡ys v∈xs = subst (λ x → v ∈ x) xs≡ys v∈xs

∃-last : ∀ (v : A) xs → ∃[ z ](∃[ ys ](ys ∷ʳ z ≡ v ∷ xs))
∃-last v [] = v , [] , refl
∃-last v (x ∷ xs) with ∃-last x xs
... | z , ys , ys∷ʳz≡x∷xs = z , (v ∷ ys) , cong (v ∷_) ys∷ʳz≡x∷xs

l7 : ∀ (v : A) zs {xs ys} → xs ≡ ys -> zs ∷ʳ v ++ xs ≡ zs ++ v ∷ ys
l7 v [] xs≡ys = cong (v ∷_) xs≡ys
l7 v (x ∷ zs) xs≡ys = cong (x ∷_) (l7 v zs xs≡ys)

l3 : ∀ (v : A) xs ys → xs ++ reverse (v ∷ ys) ≡ (xs ++ reverse ys) ∷ʳ v
l3 v xs ys = trans (cong (xs ++_) (unfold-reverse v ys)) (sym (++-assoc xs (reverse ys) [ v ]))

l4 : ∀ (v : A) xs {ys} → xs ∷ʳ v ++ ys ≡ xs ++ v ∷ ys
l4 v [] = refl
l4 v (x ∷ xs) = cong (x ∷_) (l4 v xs)

l11 : ∀ (v : A) xs ys → reverse xs ++ v ∷ ys ≡ reverse (v ∷ xs) ++ ys
l11 v xs ys = trans (sym (l4 v (reverse xs))) (cong (_++ ys) (sym (unfold-reverse v xs)))

l9 : ∀ (v : A) xs ys zs → xs ∷ʳ v ↭ ys ++ v ∷ zs -> xs ↭ ys ++ zs
l9 v xs ys zs x∷ʳv↭ys++v∷zs = subst (λ x → x ↭ _) (++-identityʳ xs) (drop-mid xs ys x∷ʳv↭ys++v∷zs)

module _ {v w : A} where

  ∈-comb : ∀ {xs} ys {zs} → xs ≡ ys ++ [ v ] ++ zs -> v ∈ xs
  ∈-comb ys xs≡ = subst (λ ls → v ∈ ls) (sym xs≡) (∈-insert ys)


  ∈-∷ʳ : ∀ xs {ys} → v ∈ xs ++ ys -> v ∈ xs ∷ʳ w ++ ys
  ∈-∷ʳ xs v∈ with ∈-++⁻ xs v∈
  ... | inj₁ v∈xs = ∈-++⁺ˡ (∈-++⁺ˡ v∈xs)
  ... | inj₂ v∈ys = ∈-++⁺ʳ (xs ∷ʳ w) v∈ys

  -- need better names
  l1 : ∀ xs {ys} → (xs ∷ʳ v) ++ ys ≡ xs ++ [ v ] ++ ys
  l1 [] = refl
  l1 (x ∷ xs) = cong (x ∷_) (l1 xs)

  l2 : ∀ xs ys zs → xs ∷ʳ v ↭ ys ∷ʳ v ++ zs -> xs ↭ ys ++ zs
  l2 xs ys zs xs∷ʳv↭ys∷ʳv++zs with drop-mid xs ys (subst (λ x → xs ∷ʳ v ↭ x) (l1 ys) xs∷ʳv↭ys∷ʳv++zs)
  ... | xs++[]↭ys++zs = subst (λ x → x ↭ ys ++ zs) (++-identityʳ xs) xs++[]↭ys++zs


  l5 : ∀ xs {ys} -> v ∈ xs ++ ys -> v ∉ ys -> v ∈ xs
  l5 xs v∈xs++ys v∉ys with ∈-++⁻ xs v∈xs++ys
  ... | inj₁ v∈xs = v∈xs
  ... | inj₂ v∈ys = contradiction v∈ys v∉ys

  l8 : ∀ xs {ys zs} -> xs ++ v ∷ ys ++ w ∷ zs ≡ (xs ++ v ∷ ys) ++ w ∷ zs
  l8 [] = refl
  l8 (x ∷ xs) = cong (x ∷_) (l8 xs)

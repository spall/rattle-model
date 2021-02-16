
module Functional.Script.Exec where

open import Agda.Builtin.Equality
open import Data.List using ([] ; _∷_ ; List ; map ; _++_ ; _∷ʳ_ ; [_])
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∄-syntax ; ∃-syntax ; Σ-syntax)
open import Functional.State using (F ; run ; System ; Cmd ; trace)
open import Functional.Build using (Build)
open import Functional.File using (FileName ; Files)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Relation.Binary.PropositionalEquality using (decSetoid ; trans ; sym ; subst ; cong ; cong₂) 
open import Data.String.Properties using (_≟_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_)
open import Data.List.Properties using (∷-injective ; ∷-injectiveʳ ; ∷-injectiveˡ ; ++-identityʳ)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Data.List.Relation.Unary.Any using (tail ; here)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-insert ; ∈-∃++)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)



exec : F -> System -> Build -> System
exec _ sys [] = sys
exec f sys (x ∷ b) = exec f (run f x sys) b

writes : F -> System -> Build -> List FileName
writes _ _ [] = []
writes f sys (x ∷ b) = (proj₂ (trace f sys x)) ++ writes f (run f x sys) b

outsC : F -> System -> (x : Cmd) -> (b : Build) -> x ∈ b -> Files
outsC f sys x (x₁ ∷ b) x∈b with x ≟ x₁
... | yes x≟x₁ = proj₂ (proj₁ (f x) sys)
... | no ¬x≟x₁ = outsC f (run f x₁ sys) x b (tail ¬x≟x₁ x∈b) 

writesC : F -> System -> (x : Cmd) -> (b : Build) -> x ∈ b -> List FileName
writesC f sys x (x₁ ∷ b) x∈b with x ≟ x₁
... | yes x≟x₁ = proj₂ (trace f sys x)
... | no ¬x≟x₁ = writesC f (run f x₁ sys) x b (tail ¬x≟x₁ x∈b)

readsC : F -> System -> (x : Cmd) -> (b : Build) -> x ∈ b -> List FileName
readsC f sys x (x₁ ∷ b) x∈b with x ≟ x₁
... | yes x≟x₁ = proj₁ (trace f sys x)
... | no ¬x≟x₁ = readsC f (run f x₁ sys) x b (tail ¬x≟x₁ x∈b)

getSys : F -> System -> (x : Cmd) -> (b : Build) -> x ∈ b -> System
getSys f sys x (x₁ ∷ b) x∈b with x ≟ x₁
... | yes x≟x₁ = sys
... | no ¬x≟x₁ = getSys f (run f x₁ sys) x b (tail ¬x≟x₁ x∈b)

read-writes : F -> System -> Cmd -> List FileName
read-writes f sys c = let (rs , ws) = trace f sys c in
                rs ++ ws

build-read-writes : F -> System -> Build -> List FileName -> List FileName
build-read-writes f sys [] ls = ls
build-read-writes f sys (x ∷ b) ls = build-read-writes f (run f x sys) b ((read-writes f sys x) ++ ls)


data HazardFree : F -> System -> Build -> List FileName -> Set where
  Null : {f : F} {sys : System} {ls : List FileName} -> HazardFree f sys [] ls
  Cons : {f : F} {sys : System} (c : Cmd) -> (b : Build) -> (ls : List FileName) -> Disjoint (proj₂ (trace f sys c)) ls -> HazardFree f (run f c sys) b ((read-writes f sys c) ++ ls) -> HazardFree f sys (c ∷ b) ls


{- hazards:  write-write 
             read-write
             speculative write-read: we have a reference build b; where x before y and y reads something x writes. 
                                     we have a re-ordered build b₂ ; which is also hazardfree in the above way
                                       it is a hazardfree re-ordering if ¬∃[ cmd ](cmd ∈ b₂ × ∃[ f ]( f ∈ writes cmd × ∃[ cmd₁ ](f ∈ reads cmd₁ × cmd₁ is after cmd in b₂ × cmd₁ is before cmd₂ in b)))
-}

_before_en_ : Cmd -> Cmd -> Build -> Set
x₁ before x₂ en b = ∃[ ls₁ ](∃[ ls₂ ](b ≡ ls₁ ++ [ x₁ ] ++ ls₂ × x₂ ∈ ls₂))

write-before-read : F -> System -> Cmd -> Cmd -> Build -> Set
write-before-read f sys x₁ x₂ b = ∃[ f₁ ](∃[ ls₁ ](∃[ ls₂ ](∃[ ls₃ ](b ≡ ls₁ ++ x₁ ∷ ls₂ ++ x₂ ∷ ls₃ × f₁ ∈ proj₂ (trace f (exec f sys ls₁) x₁) × f₁ ∈ proj₁ (trace f (exec f sys (ls₁ ++ x₁ ∷ ls₂)) x₂)))))

{-
speculate-wr-hazard : F -> System -> Build -> Build -> Set
speculate-wr-hazard f sys b b₂ = ∃[ x ](∃[ x₂ ](Σ[ x∈b ∈ (x ∈ b) ](Σ[ x₂∈b ∈ (x₂ ∈ b) ](Σ[ x∈b₂ ∈ (x ∈ b₂) ](Σ[ x₂∈b₂ ∈ (x₂ ∈ b₂) ](∃[ f₁ ](f₁ ∈ writesC f sys x b x∈b × f₁ ∈ readsC f sys x₂ b x₂∈b × x₂ before x en b₂)))))))


speculative-wr-hazard : F -> System -> Build -> Build -> Set
speculative-wr-hazard f sys b b₂ = ∃[ x ](∃[ x₂ ](Σ[ x∈b ∈ (x ∈ b) ](Σ[ x₂∈b ∈ (x₂ ∈ b) ](Σ[ x∈b₂ ∈ (x ∈ b₂) ](Σ[ x₂∈b₂ ∈ (x₂ ∈ b₂) ](∃[ f₁ ](f₁ ∈ writesC f sys x₂ b₂ x₂∈b₂ × f₁ ∈ readsC f sys x b₂ x∈b₂ × x₂ before x en b₂ × x before x₂ en b)))))))
-}

speculative-wr-hazard : F -> System -> Build -> Build -> Set
speculative-wr-hazard f sys b b₂ = ∃[ x₁ ](∃[ x₂ ](Σ[ x₁∈b ∈ (x₁ ∈ b) ](Σ[ x₂∈b ∈ (x₂ ∈ b) ](write-before-read f sys x₂ x₁ b₂ × x₁ before x₂ en b))))



¬speculative-wr-hazard : F -> System -> Build -> Build -> Set
¬speculative-wr-hazard f sys b b₂ = ¬ (speculative-wr-hazard f sys b b₂)


{- b₂ is the re-ordering -}
data HazardFreeReordering : F -> System -> Build -> Build -> Set where
     HFR : {f : F} {sys : System} {ls : List FileName} (b : Build) -> (b₂ : Build) -> b ↭ b₂ -> HazardFree f sys b ls -> HazardFree f sys b₂ ls -> ¬speculative-wr-hazard f sys b b₂ -> HazardFreeReordering f sys b b₂

-- proofs to go in own file eventually:

lemma3 : {f : F} {sys : System} (x : Cmd) (b₁ b₂ : Build) -> (x∈b₁ : x ∈ b₁) -> (x∈b₁++b₂ : x ∈ b₁ ++ b₂) -> readsC f sys x b₁ x∈b₁ ≡ readsC f sys x (b₁ ++ b₂) x∈b₁++b₂
lemma3 {f} {sys} x (x₁ ∷ b₁) b₂ x∈b₁ x∈b₁++b₂ with x ≟ x₁
... | yes x≟x₁ = refl
... | no ¬x≟x₁ = lemma3 {f} {run f x₁ sys} x b₁ b₂ (tail ¬x≟x₁ x∈b₁) (tail ¬x≟x₁ x∈b₁++b₂)

-- S.writesC f sys x₂ (b₁ ++ b₂) x₂∈b₁++b₂ ≡ S.writesC f sys x₂ ((b₁ ++ x ∷ []) ++ b₂) (g₃ x₂ x₂∈b₁++b₂)
lemma2 : {f : F} {sys : System} (x : Cmd) (b₁ b₂ : Build) -> (x∈b₁ : x ∈ b₁) -> (x∈b₁++b₂ : x ∈ b₁ ++ b₂) -> writesC f sys x b₁ x∈b₁ ≡ writesC f sys x (b₁ ++ b₂) x∈b₁++b₂
lemma2 {f} {sys} x (x₁ ∷ b₁) b₂ x∈b₁ x∈b₁++b₂ with x ≟ x₁
... | yes x≟x₁ = refl
... | no ¬x≟x₁ = lemma2 {f} {run f x₁ sys} x b₁ b₂ (tail ¬x≟x₁ x∈b₁) (tail ¬x≟x₁ x∈b₁++b₂)

g₁ : {f : F} {sys : System} (x x₂ : Cmd) (b₁ b₂ : Build) -> (x∈b₁ : x ∈ b₁) -> (x∈b₁++b₂ : x ∈ b₁ ++ b₂) -> (x∈b₁++[x₂]++b₂ : x ∈ b₁ ∷ʳ x₂ ++ b₂) -> writesC f sys x (b₁ ++ b₂) x∈b₁++b₂ ≡ writesC f sys x (b₁ ∷ʳ x₂ ++ b₂) x∈b₁++[x₂]++b₂
g₁ x x₂ b₁ b₂ x∈b₁ x∈b₁++b₂ x∈b₁++[x₂]++b₂ with lemma2 x b₁ b₂ x∈b₁ x∈b₁++b₂ | lemma2 x (b₁ ++ [ x₂ ]) b₂ (∈-++⁺ˡ x∈b₁) x∈b₁++[x₂]++b₂ -- {!!}
... | a | a₁ = trans (sym a) (trans (lemma2 x b₁ [ x₂ ] x∈b₁ (∈-++⁺ˡ x∈b₁)) a₁)

-- S.readsC f sys x₁ (b₁ ++ b₂) x₁∈b₁++b₂ ≡ S.readsC f sys x₁ ((b₁ ++ x ∷ []) ++ b₂) a₁
g₂ : {f : F} {sys : System} (x x₂ : Cmd) (b₁ b₂ : Build) -> (x∈b₁ : x ∈ b₁) -> (x∈b₁++b₂ : x ∈ b₁ ++ b₂) -> (x∈b₁++[x₂]++b₂ : x ∈ b₁ ∷ʳ x₂ ++ b₂) -> readsC f sys x (b₁ ++ b₂) x∈b₁++b₂ ≡ readsC f sys x (b₁ ∷ʳ x₂ ++ b₂) x∈b₁++[x₂]++b₂
g₂ x x₂ b₁ b₂ x∈b₁ x∈b₁++b₂ x∈b₁++[x₂]++b₂ with lemma3 x b₁ b₂ x∈b₁ x∈b₁++b₂ | lemma3 x (b₁ ++ [ x₂ ]) b₂ (∈-++⁺ˡ x∈b₁) x∈b₁++[x₂]++b₂
... | a | a₁ = trans (sym a) (trans (lemma3 x b₁ [ x₂ ] x∈b₁ (∈-++⁺ˡ x∈b₁)) a₁)
{-
g₃ : {f : F} {sys : System} (x x₁ : Cmd) (b₁ b₂ : Build) -> (x₁∈b₁∷ʳx++b₂ : x₁ ∈ b₁ ∷ʳ x ++ b₂) -> (x₁∈b₁++x∷b₂ : x₁ ∈ b₁ ++ x ∷ b₂) -> readsC f sys x₁ (b₁ ∷ʳ x ++ b₂) x₁∈b₁∷ʳx++b₂ ≡ readsC f sys x₁ (b₁ ++ x ∷ b₂) x₁∈b₁++x∷b₂
g₃ x x₁ b₁ b₂ x₁∈b₁∷ʳx++b₂ x₁∈b₁++x∷b₂ with ∈-++⁻ b₁ x₁∈b₁++x∷b₂
... | inj₁ x₂ = {!!}
... | inj₂ y = {!!}
-}
lemma1 : {x₁ x₂ x₃ : Cmd} (b₁ b₂ : Build) -> x₁ before x₂ en (b₁ ++ b₂) -> x₁ before x₂ en (b₁ ∷ʳ x₃ ++ b₂) 
lemma1 {x₁} {x₂} {x₃} [] b₂ (ls₁ , ls₂ , b≡ls₁++x₁∷ls₂ , x₂∈ls₂) = (x₃ ∷ ls₁) , (ls₂ , cong (x₃ ∷_) b≡ls₁++x₁∷ls₂ , x₂∈ls₂)
lemma1 {x₁} {x₂} {x₃} (x ∷ b₁) b₂ ([] , ls₂ , b≡ls₁++x₁∷ls₂ , x₂∈ls₂) with ∷-injective b≡ls₁++x₁∷ls₂
... | x≡x₁ , b₁++b₂≡ls₂ with ∈-++⁻ b₁ (subst (λ x₄ → x₂ ∈ x₄) (sym b₁++b₂≡ls₂) x₂∈ls₂)
... | inj₁ x₂∈b₁ = [] , (b₁ ∷ʳ x₃ ++ b₂ , (cong₂ _∷_ x≡x₁ refl , ∈-++⁺ˡ (∈-++⁺ˡ x₂∈b₁)))
... | inj₂ x₂∈b₂ = [] , (b₁ ∷ʳ x₃ ++ b₂ , (cong₂ _∷_ x≡x₁ refl , ∈-++⁺ʳ (b₁ ∷ʳ x₃) x₂∈b₂))
lemma1 {x₁} {x₂} {x₃} (x ∷ b₁) b₂ (x₄ ∷ ls₁ , ls₂ , b≡ls₁++x₁∷ls₂ , x₂∈ls₂) with lemma1 b₁ b₂ (ls₁ , (ls₂ , (∷-injectiveʳ b≡ls₁++x₁∷ls₂ , x₂∈ls₂)))
... | ls₃ , ls₄ , b₁++[x₃]++b₂≡ls₃++[x₁]++ls₄ , x₂∈ls₄ = x₄ ∷ ls₃ , (ls₄ , (cong₂ _∷_ (∷-injectiveˡ b≡ls₁++x₁∷ls₂) b₁++[x₃]++b₂≡ls₃++[x₁]++ls₄ , x₂∈ls₄))

lemma4 : {x₁ x₂ x₃ : Cmd} (b : Build) -> x₁ before x₂ en b -> x₁ before x₂ en (b ∷ʳ x₃)
lemma4 {x₁} {x₂} {x₃} b before with lemma1 b [] (subst (λ x → x₁ before x₂ en x) (sym (++-identityʳ b)) before)
... | a = subst (λ x → x₁ before x₂ en x) (++-identityʳ (b ++ x₃ ∷ [])) a

lemma5 : (x₁ x₂ : Cmd) -> (b : Build) -> x₁ ∈ b -> x₁ before x₂ en (b ∷ʳ x₂)
lemma5 x₁ x₂ b x₁∈b with ∈-∃++ x₁∈b
... | ls₁ , ls₂ , b≡ls₁++x₁++ls₂ = ls₁ , ls₂ ∷ʳ x₂ , trans (cong (_∷ʳ x₂) b≡ls₁++x₁++ls₂) (f₂ x₂ ls₁ (x₁ ∷ ls₂)) , ∈-++⁺ʳ ls₂  (here refl)
  where f₂ : (x₂ : Cmd) -> (ls₁ ls₂ : Build) -> (ls₁ ++ ls₂) ∷ʳ x₂ ≡ ls₁ ++ ls₂ ∷ʳ x₂
        f₂ x₂ [] ls₂ = refl
        f₂ x₂ (x ∷ ls₁) ls₂ = cong (x ∷_) (f₂ x₂ ls₁ ls₂)


module Functional.Script.Exec where

open import Common.List.Properties as CLP
open import Agda.Builtin.Equality
open import Data.Sum using (_⊎_)
open import Data.List using ([] ; _∷_ ; List ; map ; _++_ ; _∷ʳ_ ; [_])
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∄-syntax ; ∃-syntax ; Σ-syntax)
open import Functional.State as St using (F ; run ; System ; Cmd ; trace)
open import Functional.Build using (Build)
open import Functional.File using (FileName ; Files)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Relation.Binary.PropositionalEquality using (decSetoid ; trans ; sym ; subst ; cong ; cong₂) 
open import Data.String.Properties using (_≟_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Data.List.Properties using (∷-injective ; ∷-injectiveʳ ; ∷-injectiveˡ ; ++-identityʳ)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-insert ; ∈-∃++)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ ; ++⁻ʳ)


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

-- another alternative definition

write-before-read : F -> System -> Cmd -> Cmd -> Build -> Set
write-before-read f sys x₁ x₂ b = ∃[ f₁ ](∃[ xs ](∃[ ys ](∃[ zs ](b ≡ xs ++ x₁ ∷ ys ++ x₂ ∷ zs × f₁ ∈ proj₂ (trace f (exec f sys xs) x₁) × f₁ ∈ proj₁ (trace f (exec f sys (xs ++ x₁ ∷ ys)) x₂)))))

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
g₁ x x₂ b₁ b₂ x∈b₁ x∈b₁++b₂ x∈b₁++[x₂]++b₂ with lemma2 x b₁ b₂ x∈b₁ x∈b₁++b₂ | lemma2 x (b₁ ++ [ x₂ ]) b₂ (∈-++⁺ˡ x∈b₁) x∈b₁++[x₂]++b₂
... | a | a₁ = trans (sym a) (trans (lemma2 x b₁ [ x₂ ] x∈b₁ (∈-++⁺ˡ x∈b₁)) a₁)


-- S.readsC f sys x₁ (b₁ ++ b₂) x₁∈b₁++b₂ ≡ S.readsC f sys x₁ ((b₁ ++ x ∷ []) ++ b₂) a₁
g₂ : {f : F} {sys : System} (x x₂ : Cmd) (b₁ b₂ : Build) -> (x∈b₁ : x ∈ b₁) -> (x∈b₁++b₂ : x ∈ b₁ ++ b₂) -> (x∈b₁++[x₂]++b₂ : x ∈ b₁ ∷ʳ x₂ ++ b₂) -> readsC f sys x (b₁ ++ b₂) x∈b₁++b₂ ≡ readsC f sys x (b₁ ∷ʳ x₂ ++ b₂) x∈b₁++[x₂]++b₂
g₂ x x₂ b₁ b₂ x∈b₁ x∈b₁++b₂ x∈b₁++[x₂]++b₂ with lemma3 x b₁ b₂ x∈b₁ x∈b₁++b₂ | lemma3 x (b₁ ++ [ x₂ ]) b₂ (∈-++⁺ˡ x∈b₁) x∈b₁++[x₂]++b₂
... | a | a₁ = trans (sym a) (trans (lemma3 x b₁ [ x₂ ] x∈b₁ (∈-++⁺ˡ x∈b₁)) a₁)


-- really belongs in common code
∃v∈-both? : (ls₁ ls₂ : List FileName) -> ∃[ v ](v ∈ ls₁ × v ∈ ls₂) ⊎ Disjoint ls₁ ls₂
∃v∈-both? [] ls₂ = inj₂ λ ()
∃v∈-both? (x ∷ ls₁) ls₂ with x ∈? ls₂
... | yes x∈ls₂ = inj₁ (x , here refl , x∈ls₂)
... | no x∉ls₂ with ∃v∈-both? ls₁ ls₂
... | inj₁ (v , v∈ls₁ , v∈ls₂) = inj₁ (v , there v∈ls₁ , v∈ls₂)
... | inj₂ disjoint = inj₂ λ x₁ → disjoint (g₃ ls₁ (proj₂ x₁) (proj₁ x₁) , proj₂ x₁)
  where g₃ : {v : FileName} (ls₁ : List FileName) -> v ∈ ls₂ -> v ∈ x ∷ ls₁ -> v ∈ ls₁
        g₃ {v} ls₁ v∈ls₂ v∈x∷ls₁ with v ≟ x
        ... | yes v≟x = contradiction (subst (λ x₁ → x₁ ∈ ls₂) v≟x v∈ls₂) x∉ls₂
        ... | no ¬v≟x = tail ¬v≟x v∈x∷ls₁


build-reads : F -> System -> Build -> List FileName
build-reads f sys [] = []
build-reads f sys (x ∷ b) = (build-reads f (run f x sys) b) ++ (proj₁ (trace f sys x))

∈build-reads-++ : {f : F} {s : System} {ys : Build} (xs : Build) -> (v : FileName) -> v ∈ build-reads f s xs -> v ∈ build-reads f s (xs ++ ys)
∈build-reads-++ {f} {s} {ys} (x ∷ xs) v v∈ with ∈-++⁻ (build-reads f (run f x s) xs) v∈
... | inj₁ v∈-build-reads = ∈-++⁺ˡ (∈build-reads-++ {f} {run f x s} xs v v∈-build-reads)
... | inj₂ v∈reads-x = ∈-++⁺ʳ (build-reads f (run f x s) (xs ++ ys)) v∈reads-x

∈build-reads-++⁺ʳ : {f : F} {s : System} {ys : Build} (xs : Build) -> (v : FileName) -> v ∈ build-reads f (exec f s xs) ys -> v ∈ build-reads f s (xs ++ ys)
∈build-reads-++⁺ʳ [] v v∈ = v∈
∈build-reads-++⁺ʳ (x ∷ xs) v v∈ = ∈-++⁺ˡ (∈build-reads-++⁺ʳ xs v v∈)


{- we want to know if any command in b reads from a file written to by x. -}
∃cmd-reads? : {f : F} {sys : System} (ls₁ : List FileName) (b : Build) -> ∃[ x ](∃[ ls₂ ](∃[ ls₃ ](∃[ f₁ ](b ≡ ls₂ ++ x ∷ ls₃ × f₁ ∈ ls₁ × f₁ ∈ proj₁ (trace f (exec f sys ls₂) x))))) ⊎ Disjoint ls₁ (build-reads f sys b)
∃cmd-reads? ls₁ [] = inj₂ λ ()
∃cmd-reads? {f} {sys} ls₁ (x ∷ b) with ∃v∈-both? ls₁ (proj₁ (trace f sys x))
... | inj₁ (f₁ , f₁∈ls₁ , f₁∈reads-x)
  = inj₁ (x , [] , b , f₁ , refl , f₁∈ls₁ , f₁∈reads-x)
... | inj₂ dsj with ∃cmd-reads? {f} {run f x sys} ls₁ b
... | inj₁ (x₁ , ls₂ , ls₃ , f₁ , b≡ls₂++x₁∷ls₃ , f₁∈ls₁ , f₁∈reads-x₁)
  = inj₁ (x₁ , x ∷ ls₂ , ls₃ , f₁ , cong (x ∷_) b≡ls₂++x₁∷ls₃ , f₁∈ls₁ , f₁∈reads-x₁)
... | inj₂ dsj₂ = inj₂ λ x₁ → g₃ dsj dsj₂ (proj₁ x₁) (proj₂ x₁)
  where g₃ : {v : FileName} {ls₀ ls₁ ls₂ : Build} -> Disjoint ls₀ ls₂ -> Disjoint ls₀ ls₁ -> v ∈ ls₀ -> v ∈ ls₁ ++ ls₂ -> ⊥
        g₃ {v} {ls₀} {ls₁} dsj₁ dsj₂ v∈ls₀ v∈ls₁++ls₂ with ∈-++⁻ ls₁ v∈ls₁++ls₂
        ... | inj₁ v∈ls₁ = dsj₂ (v∈ls₀ , v∈ls₁)
        ... | inj₂ v∈ls₂ = dsj₁ (v∈ls₀ , v∈ls₂)

 -- (exec f (exec f sys (b₁ ++ [ x ])) ls₁) ≡ (exec f sys (b₁ ++ x ∷ ls₁))

exec≡₁ : {f : F} {sys : System} (x : Cmd) (b₁ b₂ : Build) -> exec f (exec f sys (b₁ ++ [ x ])) b₂ ≡ exec f sys (b₁ ++ x ∷ b₂)
exec≡₁ x [] b₂ = refl
exec≡₁ {f} {sys} x (x₁ ∷ b₁) b₂ = exec≡₁ {f} {run f x₁ sys} x b₁ b₂

value≡ : {f : F} {s s₁ : System} (f₁ : FileName) (xs : Build) -> s f₁ ≡ s₁ f₁ -> All (λ f₂ → s f₂ ≡ s₁ f₂) (build-reads f s xs) -> exec f s xs f₁ ≡ exec f s₁ xs f₁
value≡ f₁ [] ≡₁ all₁ = ≡₁
value≡ {f} {s} {s₁} f₁ (x ∷ xs) ≡₁ all₁ = value≡ {f} {run f x s} {run f x s₁} f₁ xs (St.lemma2 {f} {s} {s₁} x f₁ (proj₂ (f x) s s₁ λ f₂ f₂∈reads → (lookup all₁ (∈-++⁺ʳ (build-reads f (run f x s) xs) f₂∈reads))) ≡₁) (St.lemma1 {f} {s} {s₁} (build-reads f (run f x s) xs) x (++⁻ʳ (build-reads f (run f x s) xs) all₁) (++⁻ˡ (build-reads f (run f x s) xs) all₁))


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


h₁ : {f : F} {s : System} (f₁ : FileName) -> (x w : Cmd) (xs ys ls₁ ls₂ : Build) -> f₁ ∈ proj₁ (trace f (exec f s ls₁) w) -> Disjoint (proj₂ (trace f (exec f s xs) x)) (build-reads f (exec f s xs) ys) -> xs ++ ys ≡ ls₁ ++ w ∷ ls₂ -> ∃[ ls₃ ](∃[ ls₄ ](xs ∷ʳ x ++ ys ≡ ls₃ ++ w ∷ ls₄ × f₁ ∈ proj₁ (trace f (exec f s ls₃) w)))
h₁ {f} {s} f₁ x w [] ys ls₁ ls₂ f₁∈ dsj ys≡ls₁++w∷ls₂
  = (x ∷ ls₁) , ls₂ , cong (x ∷_) ys≡ls₁++w∷ls₂
  , subst (λ x₁ → f₁ ∈ map proj₁ (proj₁ x₁))
    (proj₂ (f w) (exec f s ls₁) (exec f (run f x s) ls₁)
           λ f₂ x₁ → value≡ f₂ ls₁ (St.lemma3 f₂ (proj₂ (proj₁ (f x) s)) λ x₂ → dsj (x₂ , subst (λ x₃ → f₂ ∈ build-reads f s x₃)
                                                                                                  (sym ys≡ls₁++w∷ls₂)
                                                                                                  (∈build-reads-++⁺ʳ ls₁ f₂ (∈-++⁺ʳ (build-reads f (run f w (exec f s ls₁)) ls₂) x₁))))
                     (St.lemma5 (build-reads f s ls₁) (proj₂ (proj₁ (f x) s)) λ x₂ → dsj (proj₁ x₂ , subst (λ x₃ → _ ∈ build-reads f s x₃)
                                                                                                            (sym ys≡ls₁++w∷ls₂)
                                                                                                            (∈build-reads-++ ls₁ _ (proj₂ x₂)))))
    f₁∈
h₁ f₁ x w (x₁ ∷ xs) ys [] ls₂ f₁∈ dsj x₁∷xs++ys≡w∷ls₂ with ∷-injective x₁∷xs++ys≡w∷ls₂
... | x₁≡w , _ = [] , xs ∷ʳ x ++ ys , cong₂ _∷_ x₁≡w refl , f₁∈
h₁ {f} {s} f₁ x w (x₁ ∷ xs) ys (x₂ ∷ ls₁) ls₂ f₁∈ dsj x₁∷xs++ys≡x₂∷ls₁++w∷ls₂ with ∷-injective x₁∷xs++ys≡x₂∷ls₁++w∷ls₂
... | x₁≡x₂ , xs++ys≡ls₁++w∷ls₂ with h₁ {f} {run f x₂ s} f₁ x w xs ys ls₁ ls₂ f₁∈ (subst (λ x₃ → Disjoint (proj₂ (trace f (exec f (run f x₃ s) xs) x)) (build-reads f (exec f (run f x₃ s) xs) ys)) x₁≡x₂ dsj) xs++ys≡ls₁++w∷ls₂
... | ls₃ , ls₄ , xs++x∷ys≡ls₃++w∷ls₄ , f₁∈₂ = x₂ ∷ ls₃ , ls₄ , cong₂ _∷_ x₁≡x₂ xs++x∷ys≡ls₃++w∷ls₄ , f₁∈₂


lemma5 : {f : F} {s : System} (v w x : Cmd) (xs ys : Build) -> Disjoint (proj₂ (trace f (exec f s xs) x)) (build-reads f (exec f s xs) ys) -> write-before-read f s v w (xs ++ ys) -> write-before-read f s v w (xs ∷ʳ x ++ ys)
lemma5 {f} {s} v w x [] ys dsj (f₁ , ls₁ , ls₂ , ls₃ , ys≡ls₁++v∷ls₂++w∷ls₃ , f₁∈writes-v , f₁∈reads-w)
  = f₁ , x ∷ ls₁ , ls₂ , ls₃ , cong (x ∷_) ys≡ls₁++v∷ls₂++w∷ls₃
       , subst (λ x₁ → f₁ ∈ map proj₁ (proj₂ x₁))
                (proj₂ (f v) (exec f s ls₁) (exec f s (x ∷ ls₁))
                λ f₂ f₂∈reads-v → value≡ {f} {s} {run f x s}  f₂ ls₁ (St.lemma3 f₂ (proj₂ (proj₁ (f x) s)) λ x₂ → dsj (x₂ , subst (λ x₁ → f₂ ∈ build-reads f s x₁) (sym ys≡ls₁++v∷ls₂++w∷ls₃) (∈build-reads-++⁺ʳ ls₁ f₂ (∈-++⁺ʳ (build-reads f (run f v (exec f s ls₁)) (ls₂ ++ w ∷ ls₃)) f₂∈reads-v))))
                           (St.lemma5 (build-reads f s ls₁) (proj₂ (proj₁ (f x) s)) λ x₂ → dsj (proj₁ x₂ , subst (λ x₃ → _ ∈ (build-reads f s x₃)) (sym ys≡ls₁++v∷ls₂++w∷ls₃) (∈build-reads-++ ls₁ _ (proj₂ x₂)))))
                f₁∈writes-v
       , subst (λ x₁ → f₁ ∈ map proj₁ (proj₁ x₁))
                (proj₂ (f w) (exec f s (ls₁ ++ v ∷ ls₂)) (exec f s (x ∷ ls₁ ++ v ∷ ls₂))
                λ f₂ x₁ → value≡ f₂ (ls₁ ++ v ∷ ls₂)
                (St.lemma3 f₂ (proj₂ (proj₁ (f x) s)) λ x₂ → dsj (x₂ , subst (λ x₃ → f₂ ∈ build-reads f s x₃) (trans (sym (CLP.l8 ls₁ {ls₂} {ls₃})) (sym ys≡ls₁++v∷ls₂++w∷ls₃)) (∈build-reads-++⁺ʳ (ls₁ ++ v ∷ ls₂) f₂ (∈-++⁺ʳ (build-reads f (run f w (exec f s (ls₁ ++ v ∷ ls₂))) ls₃) x₁))))
                (St.lemma5 (build-reads f s (ls₁ ++ v ∷ ls₂)) (proj₂ (proj₁ (f x) s)) λ x₂ → dsj (proj₁ x₂ , subst (λ x₃ → _ ∈ (build-reads f s x₃)) (trans (sym (l8 ls₁ {ls₂} {ls₃})) (sym ys≡ls₁++v∷ls₂++w∷ls₃)) (∈build-reads-++ (ls₁ ++ v ∷ ls₂) _ (proj₂ x₂)))))
                f₁∈reads-w
                
lemma5 {f} {s} v w x (x₁ ∷ xs) ys dsj (f₁ , [] , ls₂ , ls₃ , x₁∷xs++ys≡v∷ls₂++w∷ls₃ , f₁∈writes-v , f₁∈reads-w) with ∷-injective x₁∷xs++ys≡v∷ls₂++w∷ls₃
... | x₁≡v , xs++ys≡ls₂++w∷ls₃ with h₁ {f} {run f v s} f₁ x w xs ys ls₂ ls₃ f₁∈reads-w (subst (λ x₂ → Disjoint (proj₂ (trace f (exec f (run f x₂ s) xs) x)) (build-reads f (exec f (run f x₂ s) xs) ys)) x₁≡v dsj) xs++ys≡ls₂++w∷ls₃
... | ls₄ , ls₅ , xs++x∷ys≡ls₄++w∷ls₅ , f₁∈reads-w₂
  = f₁ , [] , ls₄ , ls₅ , cong₂ _∷_ x₁≡v xs++x∷ys≡ls₄++w∷ls₅ , f₁∈writes-v , f₁∈reads-w₂
  
lemma5 {f} {sys} v w x (x₁ ∷ xs) ys dsj (f₁ , x₂ ∷ ls₁ , ls₂ , ls₃ , x₁∷xs++ys≡x₂∷ls₁++v∷ls₂++w∷ls₃ , f₁∈writes-v , f₁∈reads-w) with ∷-injective x₁∷xs++ys≡x₂∷ls₁++v∷ls₂++w∷ls₃
... | x₁≡x₂ , xs++ys≡ls₁++v∷ls₂++w∷ls₃ with lemma5 {f} {run f x₂ sys} v w x xs ys (subst (λ x₃ → Disjoint (proj₂ (trace f (exec f (run f x₃ sys) xs) x)) (build-reads f (exec f (run f x₃ sys) xs) ys)) x₁≡x₂ dsj) (f₁ , ls₁ , ls₂ , ls₃ , xs++ys≡ls₁++v∷ls₂++w∷ls₃ , f₁∈writes-v , f₁∈reads-w)
... | f₂ , ls₄ , ls₅ , ls₆ , xs∷ʳx++ys≡ls₄++v∷ls₅++w∷ls₆ , f₂∈writes-v , f₂∈reads-w
  = f₂ , x₂ ∷ ls₄ , ls₅ , ls₆ , cong₂ _∷_ x₁≡x₂ xs∷ʳx++ys≡ls₄++v∷ls₅++w∷ls₆ , f₂∈writes-v , f₂∈reads-w

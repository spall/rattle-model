
module Functional.Proofs where

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool

open import Relation.Binary.Definitions using (Decidable)
open import Data.Sum using (_⊎_)
open import Data.List using ([] ; List ; _++_ ; _∷_ ; map ; foldr ; _∷ʳ_ ; length ; reverse ; foldl ; [_])
open import Data.List.Properties using (++-assoc ; unfold-reverse ; ++-identityʳ ; reverse-involutive)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; ∃-syntax ; _×_ ; Σ-syntax)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-decidable ; ≡×≡⇒≡ ; ≡⇒≡×≡ ; ×-decSetoid)
open import Functional.State using (F ; System ; empty ; trace ; Cmd ; run ; extend ; inputs ; read)
open import Functional.Build using (Build)
open import Functional.Script.Exec as S using (HazardFree ; writes ; Cons ; HazardFreeReordering ; HFR ; speculate-wr-hazard ; getSys ; outsC; _before_en_)
open import Functional.Forward.Exec as Forward hiding (run)
open import Functional.File using (FileName ; Files ; File)
open import Functional.Rattle.Exec as Rattle hiding (run)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_ ; ↭-sym ; ↭-refl)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭ ; ↭-length ; drop-mid)
open import Data.String using (String)
open import Data.String.Properties using (_≟_ ; ≡-setoid ; _==_ ; ≡-decSetoid)
open import Relation.Binary.PropositionalEquality using (trans ; sym ; decSetoid ; setoid ; cong₂ ; cong ; inspect ; cong-app ; subst)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Data.List.Membership.DecSetoid (×-decSetoid ≡-decSetoid ≡-decSetoid) as P hiding (_∉_ ; _∈?_ ; _∈_)
open import Relation.Nullary using (yes ; no) 
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_ ; _⊇_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-trans ; All-resp-⊇)
open import Data.List.Relation.Unary.Any using (there ; here ; tail ; satisfied)
open import Data.List.Relation.Unary.Any.Properties using (++⁻ ; ++⁺ˡ)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-++⁻ ; ∈-insert)
-- open import Data.List.Membership.Setoid.Properties using (∈-++⁻)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (¬_)
open import Data.List.Relation.Unary.All using (All ; lookup ; all?)
open import Data.List.Relation.Unary.All.Properties using (¬All⇒Any¬)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (≡-dec)
open import Relation.Nullary.Decidable.Core using (map′)
open import Function using (_∘₂_ ; _∘_)
open import Data.List.Relation.Binary.Equality.DecPropositional ((map′ ≡×≡⇒≡ ≡⇒≡×≡) ∘₂ (×-decidable _≟_ _≟_)) using (_≡?_)

open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint ; contractᵣ)


{- if cmd does not write to file given sys; then value of file in sys is same before and after cmd runs -}
lemma10 : {f : F} {sys : System} (cmd : Cmd) -> (f₁ : FileName) -> f₁ ∉ proj₂ (trace f sys cmd) -> sys f₁ ≡ run f cmd sys f₁
lemma10 {f} {sys} cmd f₁ p = g (proj₂ (proj₁ (f cmd) sys)) p
  where g : (ls : Files) -> f₁ ∉ map proj₁ ls -> sys f₁ ≡ foldr extend sys ls f₁
        g [] p = refl
        g ((f₂ , v₂) ∷ ls) p with f₂ ≟ f₁
        ... | yes f₂≡f₁ = contradiction (here (sym f₂≡f₁)) p
        ... | no ¬f₂≡f₁ = g ls λ x → p (there x)
        

{- if build does not write to file given sys; then value of file in sys is same before and after build runs -}
lemma9 : {f : F} {sys : System} (f₁ : FileName) -> (b : Build) -> f₁ ∉ writes f sys b -> S.exec f sys b f₁ ≡ sys f₁
lemma9 f₁ [] p = refl
lemma9 {f} {sys} f₁ (x ∷ b) p with lemma9 {f} {run f x sys} f₁ b (λ x₁ → p (∈-++⁺ʳ (proj₂ (trace f sys x)) x₁)) | lemma10 {f} {sys} x f₁ λ x₁ → p (∈-++⁺ˡ x₁)
... | a | a₁ = trans a (sym a₁)



{- if running 2 builds produces different results then either the last command produced different 
results or a command before. 

if you have 2 re-ordered builds and they produce different results then there is some command that produced different results ; and you execute them in same env;

 if you have 2 builds and they dont produce the same result then they must write a different value to some file
 there must be a command that wrote to the file 

 
 if a build is hazard free then only 1 command writes to a file. 
 

 if you have 2 hazardfreereordering builds and they both have f in the output then the same command must have written to them in both. 

prove by strong inductions on builds ; 

command behaves the same if commands are added after it.

so x is at the end in one of the builds
so look at last command from other build. and drop it from both builds; by assumption it is before x in one build and after x₁ in the other, which means it doesnt write to x's inputs or outputs otherwise a hazard. so dropping it doesnt change the behavior of x. repeat until we x is at the end of both builds. 

--- a simpler proof ----

assume in one build x is the last command; without loss of generality
look at last command, if it is x, then drop x and apply induction hypothesis. 

else x₁ in re-ordered build. drop x₁ from both builds. 
-}

{- if we remove the last command from a build, the build is still hazardfree -}
lemmaA3 : {f : F} {sys : System} {ls : List String} (x : Cmd) (b : Build) -> HazardFree f sys (b ∷ʳ x) ls -> HazardFree f sys b ls
lemmaA3 x [] hf = HazardFree.Null
lemmaA3 {f} {sys} x (x₁ ∷ b) (Cons .x₁ .(b ++ x ∷ []) ls x₂ hf) = Cons x₁ b ls x₂ (lemmaA3 {f} {run f x₁ sys} x b hf)


helper : (x : Cmd) (b b₁ : Build) -> b ++ reverse (x ∷ b₁) ≡ (b ++ reverse b₁) ∷ʳ x
helper x b b₁ = trans (cong (b ++_) (unfold-reverse x b₁)) (sym (++-assoc b (reverse b₁) (x ∷ [])))

{- the prefix of a hazardfree build is still hazardfree -}
{- do we need this lemma if we have lemmA3? -}
lemma????? : {f : F} {sys : System} {ls : List String} (x : Cmd) (b b₁ : Build) -> HazardFree f sys (b ++ (reverse (x ∷ b₁))) ls -> HazardFree f sys b ls
lemma????? x [] b₁ hf = HazardFree.Null
lemma????? x (x₁ ∷ b) [] hf = lemmaA3 x (x₁ ∷ b) hf
lemma????? {f} {sys} {ls} x (x₁ ∷ b) (x₂ ∷ b₁) hf with lemmaA3 x ((x₁ ∷ b) ++ (reverse (x₂ ∷ b₁))) (subst (λ x₃ → HazardFree f sys x₃ ls) (helper x (x₁ ∷ b) (x₂ ∷ b₁)) hf)
... | hf₁ = lemma????? x₂ (x₁ ∷ b) b₁ hf₁

last : (x : Cmd) (b : Build) -> ∃[ x₁ ](∃[ b₁ ](b₁ ∷ʳ x₁ ≡ x ∷ b))
last x [] = x , ([] , refl)
last x (x₁ ∷ b) with last x₁ b
... | x₂ , b₁ , b∷ʳx₂≡x₁∷b = x₂ , ((x ∷ b₁) , cong (x ∷_) b∷ʳx₂≡x₁∷b)

{- appending a command to the end of a build is still hazardfree if we know the cmd doesnt write to anything in ls -}
lemmaX1 : {f : F} {sys : System} {ls : List String} (x : Cmd) (b : Build) -> Disjoint (proj₂ (trace f (S.exec f sys b) x)) (S.build-read-writes f sys b ls) -> HazardFree f sys b ls -> HazardFree f sys (b ∷ʳ x) ls
lemmaX1 {f} {sys} {ls} x [] ds hf = Cons x [] ls ds HazardFree.Null
lemmaX1 {f} {sys} {ls} x (x₁ ∷ b) ds (Cons .x₁ .b .ls x₂ hf) with lemmaX1 {f} {run f x₁ sys} {(S.read-writes f sys x₁) ++ ls} x b ds hf
... | a = Cons x₁ (b ∷ʳ x) ls x₂ a

helper3 : {f : F} {sys : System} (x : Cmd) (b : Build) -> run f x (S.exec f sys b) ≡ S.exec f sys (b ∷ʳ x)
helper3 x [] = refl
helper3 {f} {sys} x (x₁ ∷ b) = helper3 {f} {run f x₁ sys} x b

helper4 : {f : F} {sys : System} {ls : List String} (x : Cmd) (b : Build) -> S.read-writes f (S.exec f sys b) x ++ S.build-read-writes f sys b ls ≡ S.build-read-writes f sys (b ∷ʳ x) ls
helper4 x [] = refl
helper4 {f} {sys} {ls} x (x₁ ∷ b) = helper4 {f} {run f x₁ sys} {S.read-writes f sys x₁ ++ ls} x b

helper5 : (x : Cmd) (b b₁ : Build) -> (b ∷ʳ x ++ b₁) ≡ b ++ x ∷ b₁
helper5 x [] b₁ = refl
helper5 x (x₁ ∷ b) b₁ = cong (x₁ ∷_) (helper5 x b b₁)



{- appending a build to the end of a hazardfree build is still hazardfree if the 2nd build is hazardfree given the list of files read/written by the first build and the ending system -}
lemmaX2 : {f : F} {sys : System} {ls : List String} (b b₁ : Build) -> HazardFree f sys b ls -> HazardFree f (S.exec f sys b) b₁ (S.build-read-writes f sys b ls) -> HazardFree f sys (b ++ b₁) ls
lemmaX2 {f} {sys} {ls} b [] hf-b hf-b₁ = subst (λ x → HazardFree f sys x ls) (sym (++-identityʳ b)) hf-b
lemmaX2 {f} {sys} {ls} b (x ∷ b₁) hf-b (Cons .x .b₁ .(S.build-read-writes f sys b ls) x₁ hf-b₁) with lemmaX1 {f} {sys} {ls} x b x₁ hf-b
... | hf-b∷ʳx with lemmaX2 {f} {sys} {ls} (b ∷ʳ x) b₁ hf-b∷ʳx (subst (λ x₂ → HazardFree f (S.exec f sys (b ∷ʳ x)) b₁ x₂) (helper4 {f} {sys} x b) (subst (λ x₂ → HazardFree f x₂ b₁ ((S.read-writes f (S.exec f sys b) x) ++ S.build-read-writes f sys b ls)) (helper3 {f} {sys} x b) hf-b₁))
... | a = subst (λ x₂ → HazardFree f sys x₂ ls) (helper5 x b b₁) a


{- get hazardfree suffix of hazardfree build -}
suffix-hazardfree : {f : F} {sys : System} {ls : List String} (b b₁ : Build) -> HazardFree f sys (b ++ b₁) ls -> HazardFree f (S.exec f sys b) b₁ (S.build-read-writes f sys b ls)
suffix-hazardfree [] b₁ hf = hf
suffix-hazardfree {f} {sys} {ls} (x ∷ b) b₁ (Cons .x .(b ++ b₁) .ls x₁ hf) = suffix-hazardfree {f} {run f x sys} {S.read-writes f sys x ++ ls} b b₁ hf

helper6 : (x x₁ : Cmd) (b b₁ : Build) -> (b ∷ʳ x) ++ x₁ ∷ b₁ ≡ b ++ x ∷ x₁ ∷ b₁
helper6 x x₁ [] b₁ = refl
helper6 x x₁ (x₂ ∷ b) b₁ = cong (x₂ ∷_) (helper6 x x₁ b b₁)

build-reads : F -> System -> Build -> List FileName
build-reads f sys [] = []
build-reads f sys (x ∷ b) = (build-reads f (run f x sys) b) ++ (proj₁ (trace f sys x))

helper7 : {f : F} {sys : System} {x : Cmd} (v : String) (b : Build) -> v ∈ build-reads f sys (x ∷ b) -> v ∉ proj₁ (trace f sys x) -> v ∈ build-reads f (run f x sys) b
helper7 {f} {sys} {x} v b v∈ v∉ with ∈-++⁻ (build-reads f (run f x sys) b) v∈
... | inj₁ y = y
... | inj₂ y = contradiction y v∉


lemmaX5 : {f : F} {sys sys₁ : System} (b : Build) -> All (λ f₁ → sys f₁ ≡ sys₁ f₁) (build-reads f sys b) -> All (λ f₁ → sys f₁ ≡ sys₁ f₁) (build-reads f sys₁ b)
lemmaX5 b all = {!!}

g : {f : F} {sys sys₁ : System} (x : Cmd) -> (f₁ : FileName) -> proj₁ (f x) sys ≡ proj₁ (f x) sys₁ -> sys f₁ ≡ sys₁ f₁ -> run f x sys f₁ ≡ run f x sys₁ f₁
g {f} {sys} {sys₁} x f₁ ≡₁ ≡₂ with f₁ ∈? proj₂ (trace f sys x)
... | no f₁∉x-sys = trans (g₁ (proj₂ (proj₁ (f x) sys)) f₁ f₁∉x-sys) (trans ≡₂ (sym (g₁ (proj₂ (proj₁ (f x) sys₁)) f₁ (subst (λ x₁ → f₁ ∉ (map proj₁ (proj₂ x₁))) ≡₁ f₁∉x-sys))))
  where g₁ : {sys : System} (ls₁ : Files) -> (x₁ : FileName) -> x₁ ∉ map proj₁ ls₁ -> foldr extend sys ls₁ x₁ ≡ sys x₁
        g₁ [] x₁ x₁∉ls₁ = refl
        g₁ ((f₁ , _) ∷ ls₁) x₁ x₁∉ls with f₁ ≟ x₁ | inspect (_==_ f₁) x₁
        ... | yes f₁≟x₁ | _ = contradiction (here (sym f₁≟x₁)) x₁∉ls
        ... | no ¬f₁≟x₁ | b = g₁ ls₁ x₁ λ x₃ → x₁∉ls (there x₃)
... | yes f₁∈x-sys with g₁ {sys} {sys₁} (proj₂ (proj₁ (f x) sys)) f₁ f₁∈x-sys
  where g₁ : {sys sys₁ : System} (ls₁ : Files) -> (x₁ : FileName) -> x₁ ∈ map proj₁ ls₁ -> ∃[ v₁ ](foldr extend sys ls₁ x₁ ≡ just v₁ × foldr extend sys₁ ls₁ x₁ ≡ just v₁)
        g₁ ((f₁ , v) ∷ ls₁) x₁ x₁∈ with f₁ ≟ x₁ | inspect (_==_ f₁) x₁
        ... | yes f₁≟x₁ | b = v , refl , refl
        ... | no ¬f₁≟x₁ | b = g₁ ls₁ x₁ (tail (λ x → ¬f₁≟x₁ (sym x)) x₁∈)
... | v , snd , snd₁ = trans snd (sym (subst (λ x₁ → foldr extend sys₁ (proj₂ x₁) f₁ ≡ just v) ≡₁ snd₁))


{- Disjoint (writes x) ls -}
{- if x's inputs are the same in both systems then everything in ls will still be
   the same in the new systems after running x in both -}
lemmaX6 : {f : F} {sys sys₁ : System} (ls : List FileName) -> (x : Cmd) -> All (λ f₁ → sys f₁ ≡ sys₁ f₁) (proj₁ (trace f sys x)) -> All (λ f₁ → sys f₁ ≡ sys₁ f₁) ls -> All (λ f₁ → run f x sys f₁ ≡ run f x sys₁ f₁) ls
lemmaX6 [] x all₁ all = All.[]
lemmaX6 {f} {sys} {sys₁} (x₁ ∷ ls) x all₁ (px All.∷ all) with proj₂ (f x) sys sys₁ λ f₁ x₂ → lookup all₁ x₂
... | a = (g {f} {sys} {sys₁} x x₁ a px) All.∷ (lemmaX6 {f} {sys} {sys₁} ls x all₁ all)


g₂ : {v : String} {f : F} {sys sys₁ : System} -> (x : Cmd) -> proj₁ (f x) sys₁ ≡ proj₁ (f x) sys -> v ∈ proj₂ (trace f sys₁ x) -> v ∈ proj₂ (trace f sys x)
g₂ {v} x ≡₁ v∈ = subst (λ x₁ → v ∈ map proj₁ (proj₂ x₁)) ≡₁ v∈

{- -}
lemmaX4 : {f : F} {sys sys₁ : System} {ls₀ ls : List String} (b : Build) -> HazardFree f sys b (ls₀ ++ ls) -> All (λ f₁ → sys f₁ ≡ sys₁ f₁) (build-reads f sys b) -> HazardFree f sys₁ b ls
lemmaX4 [] hf all = HazardFree.Null
lemmaX4 {f} {sys} {sys₁} {ls₀} {ls} (x ∷ b) (Cons .x .b ls₁ x₁ hf) all with proj₂ (f x) sys sys₁ λ f₁ x₂ → lookup (All-resp-⊇ (λ x₃ → ∈-++⁺ʳ (build-reads f (run f x sys) b) x₃) all) x₂
... | a = Cons x b ls (λ x₂ → x₁ (g₂ x (sym a) (proj₁ x₂), (∈-++⁺ʳ ls₀ (proj₂ x₂)))) (lemmaX4 b hf (lemmaX6 {f} {sys} {sys₁} (build-reads f (run f x sys) b) x (All-resp-⊇ (λ x₂ → (∈-++⁺ʳ (build-reads f (run f x sys) b) x₂)) all) (All-resp-⊇ (λ x₂ → ∈-++⁺ˡ x₂) all)))


{- if we remove x from the middle of the build, it is still hazardfree if we know that x doesn't write to anything read by b₁ -}
-- need more evidenc epassed to this function.......
lemmaA4 : {f : F} {sys : System} {ls : List String} (x : Cmd) (b b₁ : Build) -> Disjoint (proj₂ (trace f (S.exec f sys b) x)) (build-reads f (run f x (S.exec f sys b)) b₁) -> HazardFree f sys (b ∷ʳ x ++ b₁) ls -> HazardFree f sys (b ++ b₁) ls
lemmaA4 {f} {sys} {ls} x b [] ds hf = subst (λ x₁ → HazardFree f sys x₁ ls) (sym (++-identityʳ b)) (lemmaA3 x b (subst (λ x₁ → HazardFree f sys x₁ ls) (++-identityʳ (b ∷ʳ x)) hf))
lemmaA4 {f} {sys} {ls} x b (x₁ ∷ b₁) ds hf with last x₁ b₁
... | x₂ , b₂ , b₂∷ᴿx₂≡x₁∷b₁ with trans (trans (unfold-reverse x₂ (reverse b₂)) (cong (_∷ʳ x₂) (reverse-involutive b₂))) b₂∷ᴿx₂≡x₁∷b₁
... | a with lemma????? x₂ (b ++ [ x ]) (reverse b₂) (subst (λ x₃ → HazardFree f sys ((b ++ x ∷ []) ++ x₃) ls) (sym a) hf)
... | hf₁ with lemmaA3 x b hf₁ | suffix-hazardfree {f} {sys} {ls} b (x ∷ x₁ ∷ b₁) (subst (λ x₃ → HazardFree f sys x₃ ls) (helper6 x x₁ b b₁) hf)
... | hf₂ | Cons .x .(x₁ ∷ b₁) .(S.build-read-writes f sys b ls) x₃ hf₃ = lemmaX2 {f} {sys} {ls} b (x₁ ∷ b₁) hf₂ (lemmaX4 {f} {run f x (S.exec f sys b)} {S.exec f sys b} (x₁ ∷ b₁) hf₃ (g₁ {S.exec f sys b} x (build-reads f (run f x (S.exec f sys b)) (x₁ ∷ b₁)) ds))
  where g₁ : {sys₁ : System} (x : Cmd) -> (ls : List FileName) -> Disjoint (proj₂ (trace f sys₁ x)) ls -> All (λ f₁ → run f x sys₁ f₁ ≡ sys₁ f₁) ls
        g₁ x [] ds = All.[]
        g₁ {sys₁} x (x₁ ∷ ls) ds with x₁ ∈? proj₂ (trace f sys₁ x)
        ... | yes x₁∈ = contradiction (x₁∈ , here refl) ds
        ... | no x₁∉ = (sym (lemma10 {f} {sys₁} x x₁ x₁∉)) All.∷ (g₁ x ls λ x₆ → ds ((proj₁ x₆) , there (proj₂ x₆)))

lemmaB1 : {f : F} {sys : System} (x : Cmd) (b b₁ b₂ : Build) -> S.¬speculative-wr-hazard f sys (b ∷ʳ x) (b₁ ∷ʳ x ++ b₂) -> S.¬speculative-wr-hazard f sys b (b₁ ++ b₂)
lemmaB1 {f} {sys} x b b₁ b₂ ¬sp-wr-hz = λ x₁ → ¬sp-wr-hz (g₁ x₁)
  where g₃ : {b₁ b₂ : Build} {x₂ : Cmd} (x : Cmd) -> x ∈ b₁ ++ b₂ -> x ∈ b₁ ∷ʳ x₂ ++ b₂
        g₃ {b₁} {b₂} {x₂} x x∈ with ∈-++⁻ b₁ x∈
        ... | inj₁ y = ∈-++⁺ˡ (∈-++⁺ˡ y)
        ... | inj₂ y = ∈-++⁺ʳ (b₁ ∷ʳ x₂) y
        g₁ : S.speculative-wr-hazard f sys b (b₁ ++ b₂) -> S.speculative-wr-hazard f sys (b ∷ʳ x) (b₁ ∷ʳ x ++ b₂)
        g₁ srwh = {!!}

{-
with ∈-++⁻ b₁ x₂∈b₁++b₂  -- | ∈-++⁻ b₁ x₂∈b₁++b₂
-- x₂ is after x in this new list we are constructing; so conceptually x either writes to something x₂ reads or it doesn't; if it does we have a new hazard; if it doesnt we should have our old hazard.
        -- prove that x₁ is in b₂ since x₁ is after x₂
        ... | inj₂ x₂∈b₂ = {!!}
        ... | inj₁ x₂∈b₁ with ∈-++⁻ b₁ x₁∈b₁++b₂
        ... | inj₂ x₁∈b₂ = {!!}
        
        ... | inj₁ x₁∈b₁ with (g₃ {b₁} {b₂} x₁ x₁∈b₁++b₂) | (g₃ {b₁} {b₂} x₂ x₂∈b₁++b₂)
        ... | a₁ | a₂ 
          = x₁ , x₂ , ∈-++⁺ˡ x₁∈b , ∈-++⁺ˡ x₂∈b , a₁ , a₂ , f₁ , (subst (λ x₃ → f₁ ∈ x₃) (S.g₁ x₂ x b₁ b₂ x₂∈b₁ x₂∈b₁++b₂ a₂) f₁∈writes-x₂)
          , (subst (λ x₃ → f₁ ∈ x₃) (S.g₂ x₁ x b₁ b₂ x₁∈b₁ x₁∈b₁++b₂ a₁) f₁∈reads-x₁) , (S.lemma1 b₁ b₂ before₁) , (S.lemma4 b before₂)
-}

helper10 : (x : Cmd) (b₁ b₂ ls₁ ls₂ : Build) -> b₂ ≡ ls₁ ++ ls₂ -> (b₁ ++ x ∷ []) ++ b₂ ≡ b₁ ++ x ∷ ls₁ ++ ls₂
helper10 x [] b₂ ls₁ ls₂ b₁≡ = cong (x ∷_) b₁≡
helper10 x (x₁ ∷ b₁) b₂ ls₁ ls₂ b₁≡ = cong (x₁ ∷_) (helper10 x b₁ b₂ ls₁ ls₂ b₁≡)

lemmaB2 : {f : F} {sys : System} (x : Cmd) (b b₁ b₂ : Build) -> HazardFreeReordering f sys (b ∷ʳ x) (b₁ ∷ʳ x ++ b₂) -> Disjoint (proj₂ (trace f (S.exec f sys b₁) x)) (build-reads f (S.exec f sys (b₁ ∷ʳ x)) b₂)
lemmaB2 {f} {sys} x b b₁ b₂ (HFR .(b ++ x ∷ []) .((b₁ ++ x ∷ []) ++ b₂) x₁ x₂ x₃ x₄) = λ x₅ → x₄ (g₁ {f} {sys} x₁ (proj₁ x₅) (proj₂ x₅))
  where g₃ : {f : F} {sys : System} (v : String) -> (b₂ : Build) -> v ∈ build-reads f sys b₂ -> ∃[ x₁ ](∃[ ls₁ ](∃[ ls₂ ](b₂ ≡ ls₁ ++ x₁ ∷ ls₂ × v ∈ proj₁ (trace f (S.exec f sys ls₁) x₁))))
        g₃ {f} {sys} v (x ∷ b₂) v∈build-reads with v ∈? proj₁ (trace f sys x)
        ... | yes v∈ = x , [] , b₂ , refl , v∈
        ... | no v∉ with g₃ {f} {run f x sys} v b₂ (helper7 v b₂ v∈build-reads v∉)
        ... | x₁ , ls₁ , ls₂ , b₂≡ls₁++x₁∷ls₂ , v∈reads-x₁ = x₁ , x ∷ ls₁ , ls₂ , cong (x ∷_) b₂≡ls₁++x₁∷ls₂ , v∈reads-x₁
        g₄ : {f : F} {sys : System} {x : Cmd} (b₁ ls₁ : Build) -> S.exec f (S.exec f sys (b₁ ∷ʳ x)) ls₁ ≡ S.exec f sys (b₁ ++ x ∷ ls₁)
        g₄ [] ls₁ = refl
        g₄ {f} {sys} (x ∷ b₁) ls₁ = g₄ {f} {run f x sys} b₁ ls₁
        g₆ : (x : Cmd) (b₁ b₂ : Build) -> (b₁ ++ x ∷ []) ++ b₂ ≡ b₁ ++ [ x ] ++ b₂
        g₆ x [] b₂ = refl
        g₆ x (x₁ ∷ b₁) b₂ = cong (x₁ ∷_) (g₆ x b₁ b₂)
        g₅ : (x : Cmd) (b b₁ b₂ : Build) -> b ++ x ∷ [] ↭ (b₁ ++ x ∷ []) ++ b₂ -> b ↭ b₁ ++ b₂
        g₅ x b b₁ b₂ ↭₁ with drop-mid b b₁ (subst (λ x₆ → b ∷ʳ x ↭ x₆) (g₆ x b₁ b₂) ↭₁)
        ... | a = subst (λ x₆ → x₆ ↭ b₁ ++ b₂) (++-identityʳ b) a
        g₁ : {f : F} {sys : System} {v : String} -> b ∷ʳ x ↭ b₁ ∷ʳ x ++ b₂ -> v ∈ proj₂ (trace f (S.exec f sys b₁) x) -> v ∈ build-reads f (S.exec f sys (b₁ ∷ʳ x)) b₂ -> S.speculative-wr-hazard f sys (b ∷ʳ x) (b₁ ∷ʳ x ++ b₂)
        g₁ {f} {sys} {v} ↭₁ v∈₁ v∈₂ with g₃ {f} {S.exec f sys (b₁ ∷ʳ x)} v b₂ v∈₂
        ... | x₁ , ls₁ , ls₂ , b₂≡ls₁++x₁∷ls₂ , v∈reads-x₁ = x₁ , x
            , ∈-resp-↭ (↭-sym ↭₁) (∈-++⁺ʳ (b₁ ∷ʳ x) (subst (λ x₅ → x₁ ∈ x₅) (sym b₂≡ls₁++x₁∷ls₂) (∈-insert ls₁))) , ∈-++⁺ʳ b (here refl)
            , (v , b₁ , ls₁ , ls₂ , (helper10 x b₁ b₂ ls₁ (x₁ ∷ ls₂) b₂≡ls₁++x₁∷ls₂) , v∈₁ , subst (λ x₅ → v ∈ proj₁ (trace f x₅ x₁)) (g₄ b₁ ls₁) v∈reads-x₁)
            , S.lemma5 x₁ x b (∈-resp-↭ (↭-sym (g₅ x b b₁ b₂ ↭₁)) (∈-++⁺ʳ b₁ (subst (λ x₅ → x₁ ∈ x₅) (sym b₂≡ls₁++x₁∷ls₂) (∈-insert ls₁))))

lemmaA2 : {f : F} {sys : System} (x : Cmd) (b b₁ b₂ : Build) -> HazardFreeReordering f sys (b ∷ʳ x) (b₁ ∷ʳ x ++ b₂) -> HazardFreeReordering f sys b (b₁ ++ b₂)
lemmaA2 {f} {sys} x b b₁ b₂ hfr@(HFR b₃ b₄  b₃↭b₄ hf hf₁ ¬sp-wr-haz) = HFR b (b₁ ++ b₂) (g₁ b₃↭b₄) (lemmaA3 x b hf) (lemmaA4 x b₁ b₂ (g₃ hfr) hf₁) (lemmaB1 x b b₁ b₂ ¬sp-wr-haz)
  where g₁ : b ∷ʳ x ↭ b₁ ∷ʳ x ++ b₂ -> b ↭ b₁ ++ b₂
        g₁ a = subst (λ x₁ → x₁ ↭ b₁ ++ b₂) (++-identityʳ b) (drop-mid b b₁ (subst (λ x₁ → b ∷ʳ x ↭ x₁) (helper5 x b₁ b₂) a))
        g₄ : {sys : System} (x : Cmd) (b₁ b₂ : Build) -> build-reads f (S.exec f sys (b₁ ++ x ∷ [])) b₂ ≡ build-reads f (run f x (S.exec f sys b₁)) b₂
        g₄ x [] b₂ = refl
        g₄ {sys} x (x₁ ∷ b₁) b₂ = g₄ {run f x₁ sys} x b₁ b₂
        g₃ : HazardFreeReordering f sys (b ∷ʳ x) (b₁ ∷ʳ x ++ b₂) -> Disjoint (proj₂ (trace f (S.exec f sys b₁) x)) (build-reads f (run f x (S.exec f sys b₁)) b₂)
        g₃ hfr with lemmaB2 x b b₁ b₂ hfr
        ... | a = subst (λ x₁ → Disjoint (proj₂ (trace f (S.exec f sys b₁) x)) x₁) (g₄ x b₁ b₂) a 


writesAccu : F -> System -> Build -> List FileName -> List FileName
writesAccu f sys [] ls = ls
writesAccu f sys (x ∷ b) ls = writesAccu f (run f x sys) b ((proj₁ (trace f sys x)) ++ ls)


-- redefine writes; so first goes into list first; 
lemmaA1 : {f : F} {sys : System} (b b₁ : Build) -> length b ≡ length b₁ -> HazardFreeReordering f sys (reverse b) (reverse b₁) -> writesAccu f sys (reverse b) [] ≡ writesAccu f sys (reverse b₁) []
lemmaA1 {f} {sys} [] [] l≡ hfr = refl
lemmaA1 {f} {sys} (x ∷ b) (x₁ ∷ b₁) l≡ hfr with x ≟ x₁
... | no ¬x≟x₁ = {!!}
... | yes x≟x₁ with lemmaA1 {f} {sys} b b₁ {!!} {!!} -- use lemma??
... | a with cong {!!} a
... | a₁ = {!!}



-- if last elements are the same; remove last then prove subset build is hazardfree and recur.
-- if last elements are not the same drop x from both; prove resulting builds are still hazardfree and recur. 


lemma1 : {f : F} {sys : System} (b b₂ : Build) -> HazardFreeReordering f sys b b₂ -> ∀ f₁ → S.exec f sys b f₁ ≡ S.exec f sys b₂ f₁
lemma1 {f} {sys} b b₂ (HFR .b .b₂ x x₁ x₂ x₃) = λ f₁ → {!!}
  where g₁ : (f₁ : FileName) -> S.exec f sys b f₁ ≡ S.exec f sys b₂ f₁
        g₁ f₁ = {!!}
-- ∃[ cmd ](f₁ ∈ writesC cmd b₂ × f₁ ∉ writesC cmd b -> ∃[ f₂ ]( f₂ ∈ readsC cmd b × ¬ sys f₂ ≡ sys₁ f₂))



script-reordered : {f : F} {sys : System} (b b₂ : Build) -> HazardFreeReordering f sys b b₂ -> ∀ f₁ → S.exec f sys b f₁ ≡ S.exec f sys b₂ f₁
script-reordered {f} {sys} b b₂ hfr = λ f₁ → g₁ f₁
  where g₁ : (f₁ : FileName) -> S.exec f sys b f₁ ≡ S.exec f sys b₂ f₁
        g₁ f₁ with f₁ ∈? writes f sys b
        ... | no ¬p = trans (lemma9 {f} {sys} f₁ b ¬p) (sym (lemma9 {f} {sys} f₁ b₂ {!!}))
        ... | yes p = {!!}


{-
forward-reordered : {f : F} {sys : System} (b : Build) -> (b₂ : Build) -> b ↭ b₂ -> HazardFree f sys b ([] , []) -> HazardFree f sys b₂ ([] , []) -> ∀ f₁ → proj₁ (Forward.exec f (sys , empty) b) f₁ ≡ proj₁ (Forward.exec f (sys , empty) b₂) f₁
forward-reordered {oc} {sys} b b₂ p p₂ p₃ = λ f₁ → f {oc} {sys} f₁ b b₂ p p₂ p₃
  where f : {f : F} {sys : System} (f₁ : FileName) -> (b : Build) -> (b₂ : Build) -> b ↭ b₂ -> HazardFree f sys b ([] , []) -> HazardFree f sys b₂ ([] , []) -> proj₁ (Forward.exec f (sys , empty) b) f₁ ≡ proj₁ (Forward.exec f (sys , empty) b₂) f₁
        f {oc} {sys} f₁ b b₂ p p₂ p₃ with script-reordered {oc} {sys} b b₂ p p₂ p₃ f₁ | lemma1 {oc} {sys} b p₂ f₁ | lemma1 {oc} {sys} b₂ p₃ f₁
        ... | a | a₂ | a₃ = trans (sym a₂) (trans a a₃)
        

rattle-reordered : {f : F} {sys : System} (b : Build) -> (b₂ : Build) -> b ↭ b₂ -> HazardFree f sys b ([] , []) -> HazardFree f sys b₂ ([] , []) -> ∀ f₁ → proj₁ (Rattle.exec f (sys , empty) b) f₁ ≡ proj₁ (Rattle.exec f (sys , empty) b₂) f₁
rattle-reordered b b₂ p p₂ p₃ = λ f₁ → f f₁
  where f : {f : F} {sys : System} (f₁ : FileName) -> proj₁ (Rattle.exec f (sys , empty) b) f₁ ≡ proj₁ (Rattle.exec f (sys , empty) b₂) f₁
        f {oc} {sys} f₁ = {!!}
-}

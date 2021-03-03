
open import Functional.State as St using (F ; System ; empty ; trace ; Cmd ; run ; extend ; inputs ; read)

module Functional.Proofs (oracle : F) where

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool

open import Common.List.Properties as CLP
open import Functional.Script.Properties (oracle) as FSP

open import Relation.Binary.Definitions using (Decidable)
open import Data.Sum using (_⊎_)
open import Data.List using ([] ; List ; _++_ ; _∷_ ; map ; foldr ; _∷ʳ_ ; length ; reverse ; foldl ; [_])
open import Data.List.Properties using (++-assoc ; unfold-reverse ; ++-identityʳ ; reverse-involutive ; ∷-injective ; length-reverse)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; ∃-syntax ; _×_ ; Σ-syntax)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-decidable ; ≡×≡⇒≡ ; ≡⇒≡×≡ ; ×-decSetoid)

open import Functional.Build using (Build)
open import Functional.Script.Exec (oracle) as S using (HazardFree ; writes ; Cons ; Null ; HazardFreeReordering ; HFR ; _before_en_ ; build-reads)
open import Functional.Forward.Exec as Forward hiding (run)
open import Functional.File using (FileName ; Files ; File)
open import Functional.Rattle.Exec as Rattle hiding (run)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_ ; ↭-sym ; ↭-refl)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭ ; ↭-length ; drop-mid)
open import Data.String using (String)
open import Data.String.Properties using (_≟_ ; ≡-setoid ; _==_ ; ≡-decSetoid)
open import Relation.Binary.PropositionalEquality using (trans ; sym ; decSetoid ; setoid ; cong₂ ; cong ; inspect ; cong-app ; subst ; subst₂)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Data.List.Membership.DecSetoid (×-decSetoid ≡-decSetoid ≡-decSetoid) as P hiding (_∉_ ; _∈?_ ; _∈_)
open import Relation.Nullary using (yes ; no) 
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_ ; _⊇_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-trans ; All-resp-⊇)
open import Data.List.Relation.Unary.Any using (there ; here ; tail ; satisfied)
open import Data.List.Relation.Unary.Any.Properties using (++⁻ ; ++⁺ˡ ; reverse⁺)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-++⁻ ; ∈-insert ; ∈-∃++ )
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
lemma10 : {sys : System} (cmd : Cmd) -> (f₁ : FileName) -> f₁ ∉ proj₂ (trace oracle sys cmd) -> sys f₁ ≡ run oracle cmd sys f₁
lemma10 {sys} cmd f₁ p = g (proj₂ (proj₁ (oracle cmd) sys)) p
  where g : (ls : Files) -> f₁ ∉ map proj₁ ls -> sys f₁ ≡ foldr extend sys ls f₁
        g [] p = refl
        g ((f₂ , v₂) ∷ ls) p with f₂ ≟ f₁
        ... | yes f₂≡f₁ = contradiction (here (sym f₂≡f₁)) p
        ... | no ¬f₂≡f₁ = g ls λ x → p (there x)

-- g from agove is now in STate.agda

{- if build does not write to file given sys; then value of file in sys is same before and after build runs -}
lemma9 : {sys : System} (f₁ : FileName) -> (b : Build) -> f₁ ∉ writes sys b -> S.exec sys b f₁ ≡ sys f₁
lemma9 f₁ [] p = refl
lemma9 {sys} f₁ (x ∷ b) p with lemma9 {run oracle x sys} f₁ b (λ x₁ → p (∈-++⁺ʳ (proj₂ (trace oracle sys x)) x₁)) | lemma10 {sys} x f₁ λ x₁ → p (∈-++⁺ˡ x₁)
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









-- helper6 can be l4 b ; ys is (x₁ ∷ b₁)

-- i think this can be list agnostic
-- helper7 can be replaced by a call to l5 (build-reads f (run f x sys) b)


lemmaX5 : {sys sys₁ : System} (b : Build) -> All (λ f₁ → sys f₁ ≡ sys₁ f₁) (build-reads sys b) -> All (λ f₁ → sys f₁ ≡ sys₁ f₁) (build-reads sys₁ b)
lemmaX5 b all = {!!}

g : {sys sys₁ : System} (x : Cmd) -> (f₁ : FileName) -> proj₁ (oracle x) sys ≡ proj₁ (oracle x) sys₁ -> sys f₁ ≡ sys₁ f₁ -> run oracle x sys f₁ ≡ run oracle x sys₁ f₁
g {sys} {sys₁} x f₁ ≡₁ ≡₂ with f₁ ∈? proj₂ (trace oracle sys x)
... | no f₁∉x-sys = trans (g₁ (proj₂ (proj₁ (oracle x) sys)) f₁ f₁∉x-sys) (trans ≡₂ (sym (g₁ (proj₂ (proj₁ (oracle x) sys₁)) f₁ (subst (λ x₁ → f₁ ∉ (map proj₁ (proj₂ x₁))) ≡₁ f₁∉x-sys))))
  where g₁ : {sys : System} (ls₁ : Files) -> (x₁ : FileName) -> x₁ ∉ map proj₁ ls₁ -> foldr extend sys ls₁ x₁ ≡ sys x₁
        g₁ [] x₁ x₁∉ls₁ = refl
        g₁ ((f₁ , _) ∷ ls₁) x₁ x₁∉ls with f₁ ≟ x₁ | inspect (_==_ f₁) x₁
        ... | yes f₁≟x₁ | _ = contradiction (here (sym f₁≟x₁)) x₁∉ls
        ... | no ¬f₁≟x₁ | b = g₁ ls₁ x₁ λ x₃ → x₁∉ls (there x₃)
... | yes f₁∈x-sys with g₁ {sys} {sys₁} (proj₂ (proj₁ (oracle x) sys)) f₁ f₁∈x-sys

  where g₁ : {sys sys₁ : System} (ls₁ : Files) -> (x₁ : FileName) -> x₁ ∈ map proj₁ ls₁ -> ∃[ v₁ ](foldr extend sys ls₁ x₁ ≡ just v₁ × foldr extend sys₁ ls₁ x₁ ≡ just v₁)
        g₁ ((f₁ , v) ∷ ls₁) x₁ x₁∈ with f₁ ≟ x₁ | inspect (_==_ f₁) x₁
        ... | yes f₁≟x₁ | b = v , refl , refl
        ... | no ¬f₁≟x₁ | b = g₁ ls₁ x₁ (tail (λ x → ¬f₁≟x₁ (sym x)) x₁∈)
        
... | v , snd , snd₁ = trans snd (sym (subst (λ x₁ → foldr extend sys₁ (proj₂ x₁) f₁ ≡ just v) ≡₁ snd₁))


{- Disjoint (writes x) ls -}
{- if x's inputs are the same in both systems then everything in ls will still be
   the same in the new systems after running x in both -}

-- lemmaX6 now lemma1 in state.agda


g₂ : {v : String} {sys sys₁ : System} -> (x : Cmd) -> proj₁ (oracle x) sys₁ ≡ proj₁ (oracle x) sys -> v ∈ proj₂ (trace oracle sys₁ x) -> v ∈ proj₂ (trace oracle sys x)
g₂ {v} x ≡₁ v∈ = subst (λ x₁ → v ∈ map proj₁ (proj₂ x₁)) ≡₁ v∈

{- -}
lemmaX4 : {sys sys₁ : System} {ls₀ ls : List String} (b : Build) -> HazardFree sys b (ls₀ ++ ls) -> All (λ f₁ → sys f₁ ≡ sys₁ f₁) (build-reads sys b) -> HazardFree sys₁ b ls
lemmaX4 [] hf all = HazardFree.Null
lemmaX4 {sys} {sys₁} {ls₀} {ls} (x ∷ b) (Cons .x .b ls₁ x₁ hf) all with proj₂ (oracle x) sys sys₁ λ f₁ x₂ → lookup (All-resp-⊇ (λ x₃ → ∈-++⁺ʳ (build-reads (run oracle x sys) b) x₃) all) x₂
... | a = Cons x b ls (λ x₂ → x₁ (g₂ x (sym a) (proj₁ x₂), (∈-++⁺ʳ ls₀ (proj₂ x₂)))) (lemmaX4 b hf (St.lemma1 (build-reads (run oracle x sys) b) x (All-resp-⊇ (λ x₂ → ∈-++⁺ʳ (build-reads (run oracle x sys) b) x₂) all) (All-resp-⊇ (λ x₂ → ∈-++⁺ˡ x₂) all)))

{- if we remove x from the middle of the build, it is still hazardfree if we know that x doesn't write to anything read by b₁ -}
-- need more evidenc epassed to this function.......
lemmaA4 : {sys : System} {ls : List String} (x : Cmd) (b b₁ : Build) -> Disjoint (proj₂ (trace oracle (S.exec sys b) x)) (build-reads (run oracle x (S.exec sys b)) b₁) -> HazardFree sys (b ∷ʳ x ++ b₁) ls -> HazardFree sys (b ++ b₁) ls
lemmaA4 {sys} {ls} x b [] ds hf = subst (λ x₁ → HazardFree sys x₁ ls) (sym (++-identityʳ b)) (FSP.∷ʳ⁻ sys x b (subst (λ x₁ → HazardFree sys x₁ ls) (++-identityʳ (b ∷ʳ x)) hf))
lemmaA4 {sys} {ls} x b (x₁ ∷ b₁) ds hf with CLP.∃-last x₁ b₁ -- last x₁ b₁
... | x₂ , b₂ , b₂∷ᴿx₂≡x₁∷b₁ with trans (trans (unfold-reverse x₂ (reverse b₂)) (cong (_∷ʳ x₂) (reverse-involutive b₂))) b₂∷ᴿx₂≡x₁∷b₁
... | a with FSP.hf-++⁻ˡ sys ls x₂ (b ++ [ x ]) (reverse b₂) (subst (λ x₃ → HazardFree sys ((b ++ x ∷ []) ++ x₃) ls) (sym a) hf)
... | hf₁ with FSP.∷ʳ⁻ sys x b hf₁ | FSP.++⁻ʳ sys ls b (x ∷ x₁ ∷ b₁) (subst (λ x₃ → HazardFree sys x₃ ls) (CLP.l4 x b) hf) -- (helper6 x x₁ b b₁) hf)
... | hf₂ | Cons .x .(x₁ ∷ b₁) .(S.build-rws sys b ls) x₃ hf₃ = FSP.++⁺ sys ls b (x₁ ∷ b₁) hf₂ (lemmaX4 {run oracle x (S.exec sys b)} {S.exec sys b} (x₁ ∷ b₁) hf₃ (g₁ {S.exec sys b} x (build-reads (run oracle x (S.exec sys b)) (x₁ ∷ b₁)) ds))
  where g₁ : {sys₁ : System} (x : Cmd) -> (ls : List FileName) -> Disjoint (proj₂ (trace oracle sys₁ x)) ls -> All (λ f₁ → run oracle x sys₁ f₁ ≡ sys₁ f₁) ls
        g₁ x [] ds = All.[]
        g₁ {sys₁} x (x₁ ∷ ls) ds with x₁ ∈? proj₂ (trace oracle sys₁ x)
        ... | yes x₁∈ = contradiction (x₁∈ , here refl) ds
        ... | no x₁∉ = (sym (lemma10 {sys₁} x x₁ x₁∉)) All.∷ (g₁ x ls λ x₆ → ds ((proj₁ x₆) , there (proj₂ x₆)))

-- for helper10 just call l7 ; ys is (ls₁ ++ ls₂)

lemmaB2 : {sys : System} (x : Cmd) (b b₁ b₂ : Build) -> HazardFreeReordering sys (b ∷ʳ x) (b₁ ∷ʳ x ++ b₂) -> Disjoint (proj₂ (trace oracle (S.exec sys b₁) x)) (build-reads (S.exec sys (b₁ ∷ʳ x)) b₂)
lemmaB2 {sys} x b b₁ b₂ (HFR .(b ++ x ∷ []) .((b₁ ++ x ∷ []) ++ b₂) x₁ x₂ x₃ x₄) = λ x₅ → x₄ (g₁ {sys} x₁ (proj₁ x₅) (proj₂ x₅))

  where g₃ : {sys : System} (v : String) -> (b₂ : Build) -> v ∈ build-reads sys b₂ -> ∃[ x₁ ](∃[ ls₁ ](∃[ ls₂ ](b₂ ≡ ls₁ ++ x₁ ∷ ls₂ × v ∈ proj₁ (trace oracle (S.exec sys ls₁) x₁))))
  
        g₃ {sys} v (x ∷ b₂) v∈build-reads with ∈-++⁻ (build-reads (run oracle x sys) b₂) v∈build-reads --v ∈? proj₁ (trace oracle sys x)
        ... | inj₂ v∈₂ = x , [] , b₂ , refl , v∈₂
        ... | inj₁ v∈₁ with g₃ {run oracle x sys} v b₂ v∈₁
        ... | x₁ , ls₁ , ls₂ , b₂≡ls₁++x₁∷ls₂ , v∈reads-x₁ = x₁ , x ∷ ls₁ , ls₂ , cong (x ∷_) b₂≡ls₁++x₁∷ls₂ , v∈reads-x₁
        
        g₄ : {sys : System} {x : Cmd} (b₁ ls₁ : Build) -> S.exec (S.exec sys (b₁ ∷ʳ x)) ls₁ ≡ S.exec sys (b₁ ++ x ∷ ls₁)
        g₄ [] ls₁ = refl
        g₄ {sys} (x ∷ b₁) ls₁ = g₄ {run oracle x sys} b₁ ls₁
        
        g₁ : {sys : System} {v : String} -> b ∷ʳ x ↭ b₁ ∷ʳ x ++ b₂ -> v ∈ proj₂ (trace oracle (S.exec sys b₁) x) -> v ∈ build-reads (S.exec sys (b₁ ∷ʳ x)) b₂ -> S.speculative-wr-hazard sys (b ∷ʳ x) (b₁ ∷ʳ x ++ b₂)
        g₁ {sys} {v} ↭₁ v∈₁ v∈₂ with g₃ {S.exec sys (b₁ ∷ʳ x)} v b₂ v∈₂
        ... | x₁ , ls₁ , ls₂ , b₂≡ls₁++x₁∷ls₂ , v∈reads-x₁
          = x₁ , x , (v , b₁ , ls₁ , ls₂ , (CLP.l7 x b₁ b₂≡ls₁++x₁∷ls₂) , v∈₁ , subst (λ x₅ → v ∈ proj₁ (trace oracle x₅ x₁)) (g₄ b₁ ls₁) v∈reads-x₁)
            , S.lemma6 x₁ x b (∈-resp-↭ (↭-sym (CLP.l2 b b₁ b₂ ↭₁))
                                 (∈-++⁺ʳ b₁
                                  (subst (λ x₅ → x₁ ∈ x₅) (sym b₂≡ls₁++x₁∷ls₂) (∈-insert ls₁))))


-- (g₁ b₃↭b₄)

lemmaA2 : {sys : System} (x : Cmd) (b b₁ b₂ : Build) -> HazardFreeReordering sys (b ∷ʳ x) (b₁ ∷ʳ x ++ b₂) -> HazardFreeReordering sys b (b₁ ++ b₂)
lemmaA2 {sys} x b b₁ b₂ hfr@(HFR b₃ b₄  b₃↭b₄ hf hf₁ ¬sp-wr-haz) = HFR b (b₁ ++ b₂) (CLP.l2 b b₁ b₂ b₃↭b₄) (FSP.∷ʳ⁻ sys x b hf) (lemmaA4 x b₁ b₂ (g₃ hfr) hf₁) (S.swrh-∷ʳ⁻ sys x b b₁ b₂ ¬sp-wr-haz (g₃ hfr))
  where g₄ : {sys : System} (x : Cmd) (b₁ b₂ : Build) -> build-reads (S.exec sys (b₁ ++ x ∷ [])) b₂ ≡ build-reads (run oracle x (S.exec sys b₁)) b₂
        g₄ x [] b₂ = refl
        g₄ {sys} x (x₁ ∷ b₁) b₂ = g₄ {run oracle x₁ sys} x b₁ b₂
        -- TODO: move this lemma so it can be used elsewhere too
        g₃ : HazardFreeReordering sys (b ∷ʳ x) (b₁ ∷ʳ x ++ b₂) -> Disjoint (proj₂ (trace oracle (S.exec sys b₁) x)) (build-reads (run oracle x (S.exec sys b₁)) b₂)
        g₃ hfr with lemmaB2 x b b₁ b₂ hfr
        ... | a = subst (λ x₁ → Disjoint (proj₂ (trace oracle (S.exec sys b₁) x)) x₁) (g₄ x b₁ b₂) a


-- CwriteP≡ : -> S.CwritesP s x ≡ S.CwritesP s₁ x

-- All (λ f₁ → exec s (reverse b) f₁ ≡ exec s ls₁ f₁) (Creads (exec s ls₁ x))

-- we dont want to prove the writes are equivalent; they might not be the same order, we want to prove theyre the same sets. where order isnt important
lemmaA1 : {sys : System} (b b₁ : Build) -> length b ≡ length b₁ -> HazardFreeReordering sys (reverse b) (reverse b₁) -> ∀ f₁ → S.exec sys (reverse b) f₁ ≡ S.exec sys (reverse b₁) f₁
lemmaA1 {s} [] [] ≡₁ (HFR .[] .[] ↭₁ Null Null ¬swrh) = λ f₁ → refl
lemmaA1 {s} (x ∷ b) (x₁ ∷ b₁) ≡₁ hfr@(HFR _ _ ↭₁ hf₁ hf₂ ¬swrh) with ∈-∃++ (∈-resp-↭ ↭₁ (reverse⁺ (here refl))) 
... | ls₁ , ls₂ , reverse-b₁≡ls₁++x∷ls₂ with subst (λ x₆ → HazardFreeReordering s x₆ (reverse (x₁ ∷ b₁))) (unfold-reverse x b) hfr
... | hfr₂ with subst (λ x₆ → HazardFreeReordering s (reverse b ∷ʳ x) x₆) (trans reverse-b₁≡ls₁++x∷ls₂ (sym (CLP.l7 x ls₁ refl))) hfr₂
... | hfr₃ with subst (λ x₆ → HazardFreeReordering s (reverse b) x₆) (sym (reverse-involutive (ls₁ ++ ls₂))) (lemmaA2 {s} x (reverse b) ls₁ ls₂ hfr₃)
... | hfr₄@(HFR b₂ b₃ x₆ x₇ x₈ x₉) with trans (sym (length-reverse b)) (trans (↭-length x₆) (length-reverse (reverse (ls₁ ++ ls₂))))
... | len with lemmaA1 b (reverse (ls₁ ++ ls₂)) len hfr₄
... | ∀₁ with subst (λ x₂ → ∀ f₁ → _ ≡ S.exec s x₂ f₁) (reverse-involutive (ls₁ ++ ls₂)) ∀₁ | still-disjoint (S.exec s ls₁) x ls₂ {!!} {!!}
... | no-reverse-∀₁ | dsj₂ with S.h₄ (S.exec s (reverse b)) (S.exec s ls₁) x (all≡ s (S.Creads (S.exec s ls₁) x) (reverse b) ls₁ ls₂ dsj₂ no-reverse-∀₁)
... | ≡₃ = λ f₁ → (g₁ f₁)

-- ∀ f₁ -> f₁ ∈ reads x -> exec s xs f₁ ≡ exec s zs f₁ => result of running x in the two systems

  where g₁ : (f₁ : FileName) -> S.exec s (reverse (x ∷ b)) f₁ ≡ S.exec s (reverse (x₁ ∷ b₁)) f₁
        g₁ f₁ with f₁ ∈? proj₂ (trace oracle (S.exec s (reverse b)) x)
        ... | yes f₁∈ = {!!}


{- exec s (xs ++ ys) f₁ ≡ exec s (xs ++ x ∷ ys) f₁  if x doesnt write to f₁ 
   exec s xs f₁ ≡ exec s (zs ∷ x) f₁ 

   exec s (zs ∷ x) f₁ ≡ value x writes
   exec s (xs ++ x ∷ ys) ≡ value x writes 

-}
        g₁ f₁ | no f₁∉  with St.lemma3 {sys₁} f₁ (proj₂ (proj₁ (oracle x) sys₁)) f₁∉ | exec-∷≡ f₁ sys₂ (run oracle x sys₂) ls₂ (St.lemma5 {sys₂} (S.build-rws2 (run oracle x sys₂) ls₂) (proj₂ (proj₁ (oracle x) sys₂)) {!!}) (St.lemma3 {sys₂} f₁ (proj₂ (proj₁ (oracle x) sys₂)) (subst (λ x₂ → f₁ ∉ x₂) {!!} f₁∉)) 
          where sys₁ : System
                sys₁ = S.exec s (reverse b)
                sys₂ : System
                sys₂ = S.exec s ls₁
                dsj₃ : Disjoint (proj₂ (trace oracle sys₂ x)) (S.build-rws2 (run oracle x sys₂) ls₂)
                dsj₃ = {!!}
        ... | sys₁f₁≡ | sys₂f₁≡ with trans sys₁f₁≡ (cong-app (S.exec≡₃ x (reverse b)) f₁)
        ... | a with cong-app (subst (λ x₁ → S.exec s x₁ ≡ S.exec (S.exec s ls₁) ls₂) (sym (reverse-involutive (ls₁ ++ ls₂))) (S.exec≡₄ {s} ls₁ ls₂)) f₁
        ... | a₃ with trans (sym a) (trans (∀₁ f₁) (trans a₃ sys₂f₁≡))
        ... | a₂ with subst (λ x₁ → S.exec s x₁ f₁ ≡ _) (sym (unfold-reverse x b)) a₂
        ... | a₄ with subst (λ x₁ → _ ≡ S.exec s x₁) (sym reverse-b₁≡ls₁++x∷ls₂) (S.exec≡₅ {s} x ls₁ ls₂)
        ... | a₅  = trans a₄ (cong-app a₅ f₁)
        
        
{- todo for no case
1. f₁ ∉ writes x  => S.exec s b ≡ S.exec s (b ∷r x) 
-}


-- writes↭writes ≡ writes (reverse b) ↭ writes (reverse (reverse (ls₁ ++ ls₂)))  ≡ writes (reverse b) ↭ writes (ls₁ ++ ls₂)
{-
1. find where x is in (x₁ ∷ b₁) -- done
2. show that the length of (x₁ ∷ b₁) after it has had x removed is the same length as b -- done
3. get the hazard free re-ordering after x has been removed.  -- done
need to get the writes of x... and show its the same 
4. add writes of x into both sides of the permutation...
-}

-- if last elements are not the same drop x from both; prove resulting builds are still hazardfree and recur. 

script-reordered : {sys : System} (b b₂ : Build) -> HazardFreeReordering sys b b₂ -> ∀ f₁ → S.exec sys b f₁ ≡ S.exec sys b₂ f₁
script-reordered {sys} b b₂ hfr = λ f₁ → {!!}
{-
  where g₁ : (f₁ : FileName) -> S.exec sys b f₁ ≡ S.exec sys b₂ f₁
        g₁ f₁ with f₁ ∈? writes sys b | subst₂ (λ x x₁ → S.writesP sys x ↭ S.writesP sys x₁) (reverse-involutive b) (reverse-involutive b₂) (lemmaA1 (reverse b) (reverse b₂) {!!} {!!})
        ... | no ¬p | writes-b↭writes-b₂ = {!!} -- trans (lemma9 {sys} f₁ b ¬p) (sym (lemma9 {sys} f₁ b₂ λ x → ¬p (∈-resp-↭ (↭-sym writes-b↭writes-b₂) x)))
        ... | yes p | writes-b↭writes-b₂ = {!!}
-}

{- todo
1. reverse reverse b and b₂ in hfr
2. un reverse reverse the writes -- done

-}

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

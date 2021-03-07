
open import Functional.State as St using (F ; System ; empty ; trace ; Cmd ; run ; extend ; inputs ; read)

module Functional.Proofs (oracle : F) where

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool

open import Common.List.Properties as CLP
open import Functional.Script.Properties (oracle) as FSP hiding (++⁻ʳ)

open import Relation.Binary.Definitions using (Decidable)
open import Data.Sum using (_⊎_)
open import Data.List using ([] ; List ; _++_ ; _∷_ ; map ; foldr ; _∷ʳ_ ; length ; reverse ; foldl ; [_])
open import Data.List.Properties using (++-assoc ; unfold-reverse ; ++-identityʳ ; reverse-involutive ; ∷-injective ; length-reverse ; ++-identityˡ)
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
open import Data.List.Relation.Unary.All.Properties using (¬All⇒Any¬ ; ++⁻ˡ ; ++⁻ʳ)
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


{- i think i can use this to simplify lemmaA4 -}
lemmaX4 : {s s₁ : System} {as bs cs ls : List String} -> bs ≡ as -> (b : Build) -> HazardFree s b (as ++ cs ++ ls) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (S.reads s b) -> HazardFree s₁ b (bs ++ ls)
lemmaX4 bs≡as [] hf all₁ = HazardFree.Null
lemmaX4 {s} {s₁} {as} {bs} {cs} {ls} bs≡as (x ∷ b) (Cons .x .b _ dsj hf) all₁
  = Cons x b (bs ++ ls) (λ x₂ → dsj (g₂ x ≡₁ (proj₁ x₂) , v∈ (proj₂ x₂))) hf₁
    where ≡₁ : proj₁ (oracle x) s₁ ≡ proj₁ (oracle x) s
          ≡₁ = sym (proj₂ (oracle x) s s₁ (λ f₁ x₁ → lookup (++⁻ˡ (S.Creads s x) all₁) x₁))
          ≡₂ : S.read-writes s₁ x ≡ S.read-writes s x
          ≡₂ = subst (λ x₁ → S.read-writes s₁ x ≡ (map proj₁ (proj₁ x₁)) ++ (map proj₁ (proj₂ x₁))) ≡₁ refl
          v∈ : {v : String} -> v ∈ bs ++ ls -> v ∈ as ++ cs ++ ls
          v∈ v∈bs++ls with ∈-++⁻ bs v∈bs++ls
          ... | inj₁ v∈bs = ∈-++⁺ˡ (subst (λ x₁ → _ ∈ x₁) bs≡as v∈bs)
          ... | inj₂ v∈ls = ∈-++⁺ʳ as (∈-++⁺ʳ cs v∈ls)
          hf₁-sub : HazardFree (run oracle x s) b ((S.read-writes s x ++ as) ++ cs ++ ls)
          hf₁-sub = subst (λ x₁ → HazardFree (run oracle x s) b x₁) (sym (++-assoc (S.read-writes s x) as (cs ++ ls))) hf
          hf₁ : HazardFree (run oracle x s₁) b (S.read-writes s₁ x ++ bs ++ ls)
          hf₁ with lemmaX4 {run oracle x s} {run oracle x s₁} {S.read-writes s x ++ as} {S.read-writes s₁ x ++ bs} {cs} {ls} (cong₂ _++_ ≡₂ bs≡as) b hf₁-sub (St.lemma1 {oracle} {s} {s₁} (S.reads (run oracle x s) b) x (++⁻ˡ (S.Creads s x) all₁) (++⁻ʳ (S.Creads s x) all₁))
          ... | hf₂ = subst (λ x₁ → HazardFree (run oracle x s₁) b x₁) (++-assoc (S.read-writes s₁ x) bs ls) hf₂


{- if we remove x from the middle of the build, it is still hazardfree if we know that x doesn't write to anything read by b₁ -}
-- need more evidenc epassed to this function.......
lemmaA4 : {sys : System} {ls : List String} (x : Cmd) (b b₁ : Build) -> Disjoint (S.Cwrites (S.exec sys b) x) (S.reads (run oracle x (S.exec sys b)) b₁) -> HazardFree sys (b ++ x ∷ b₁) ls -> HazardFree sys (b ++ b₁) ls
lemmaA4 {sys} {ls} x b [] ds hf = subst (λ x₁ → HazardFree sys x₁ _) (sym (++-identityʳ b)) (FSP.∷ʳ⁻ sys x b hf)
lemmaA4 {sys} {ls} x b (x₁ ∷ b₁) ds hf with CLP.∃-last x₁ b₁ -- last x₁ b₁
... | x₂ , b₂ , b₂∷ᴿx₂≡x₁∷b₁ with trans (trans (unfold-reverse x₂ (reverse b₂)) (cong (_∷ʳ x₂) (reverse-involutive b₂))) b₂∷ᴿx₂≡x₁∷b₁
... | a with FSP.hf-++⁻ˡ sys ls x₂ (b ++ [ x ]) (reverse b₂) (subst (λ x₃ → HazardFree sys ((b ++ x ∷ []) ++ x₃) ls) (sym a) (subst (λ x₃ → HazardFree sys x₃ ls) (sym (CLP.l4 x b)) hf))
... | hf₁ with FSP.∷ʳ⁻ sys x b hf₁ | FSP.++⁻ʳ sys ls b (x ∷ x₁ ∷ b₁) hf
... | hf₂ | Cons .x .(x₁ ∷ b₁) _ x₃ hf₃ = FSP.++⁺ sys ls b (x₁ ∷ b₁) hf₂ hf₄
  where g₁ : {sys₁ : System} (x : Cmd) -> (ls : List FileName) -> Disjoint (proj₂ (trace oracle sys₁ x)) ls -> All (λ f₁ → run oracle x sys₁ f₁ ≡ sys₁ f₁) ls
        g₁ x [] ds = All.[]
        g₁ {sys₁} x (x₁ ∷ ls) ds with x₁ ∈? proj₂ (trace oracle sys₁ x)
        ... | yes x₁∈ = contradiction (x₁∈ , here refl) ds
        ... | no x₁∉ = (sym (lemma10 {sys₁} x x₁ x₁∉)) All.∷ (g₁ x ls λ x₆ → ds ((proj₁ x₆) , there (proj₂ x₆)))
        hf₄ : HazardFree (S.exec sys b) (x₁ ∷ b₁) (S.build-rws sys b ls)
        hf₄ = lemmaX4 {run oracle x (S.exec sys b)} {S.exec sys b} {[]} {[]} {S.read-writes (S.exec sys b) x} {S.build-rws sys b ls} refl (x₁ ∷ b₁) hf₃ (g₁ {S.exec sys b} x (S.reads (run oracle x (S.exec sys b)) (x₁ ∷ b₁)) ds)

lemmaA2 : {sys : System} (x : Cmd) (b b₁ b₂ : Build) -> HazardFreeReordering sys (b ∷ʳ x) (b₁ ++ x ∷ b₂) -> HazardFreeReordering sys b (b₁ ++ b₂)
lemmaA2 {sys} x b b₁ b₂ hfr@(HFR b₃ b₄  b₃↭b₄ hf hf₁ ¬sp-wr-haz) = HFR b (b₁ ++ b₂) (CLP.l9 x b b₁ b₂ b₃↭b₄) (FSP.∷ʳ⁻ sys x b hf) (lemmaA4 x b₁ b₂ (hfr→dsj sys x b b₁ b₂ hfr) hf₁) (S.swrh-∷ʳ⁻ sys x b b₁ b₂ ¬sp-wr-haz (hfr→dsj sys x b b₁ b₂ hfr))
  where g₄ : {sys : System} (x : Cmd) (b₁ b₂ : Build) -> build-reads (S.exec sys (b₁ ++ x ∷ [])) b₂ ≡ build-reads (run oracle x (S.exec sys b₁)) b₂
        g₄ x [] b₂ = refl
        g₄ {sys} x (x₁ ∷ b₁) b₂ = g₄ {run oracle x₁ sys} x b₁ b₂

-- All (λ f₁ → exec s (reverse b) f₁ ≡ exec s ls₁ f₁) (Creads (exec s ls₁ x))

-- we dont want to prove the writes are equivalent; they might not be the same order, we want to prove theyre the same sets. where order isnt important
lemmaA1 : {sys : System} (b b₁ : Build) -> length b ≡ length b₁ -> HazardFreeReordering sys (reverse b) (reverse b₁) -> ∀ f₁ → S.exec sys (reverse b) f₁ ≡ S.exec sys (reverse b₁) f₁
lemmaA1 {s} [] [] ≡₁ (HFR .[] .[] ↭₁ Null Null ¬swrh) = λ f₁ → refl
lemmaA1 {s} (x ∷ b) b₁ ≡₁ hfr@(HFR _ _ ↭₁ hf₁ hf₂ ¬swrh) with ∈-∃++ (∈-resp-↭ ↭₁ (reverse⁺ (here refl))) 
... | ls₁ , ls₂ , reverse-b₁≡ls₁++x∷ls₂ with subst₂ (λ x₁ x₂ → HazardFreeReordering s x₁ x₂) (unfold-reverse x b) reverse-b₁≡ls₁++x∷ls₂ hfr
... | hfr₁ with subst (λ x₁ → HazardFreeReordering _ _ x₁) (sym (reverse-involutive (ls₁ ++ ls₂))) (lemmaA2 {s} x (reverse b) ls₁ ls₂ hfr₁)
... | hfr₂@(HFR _ _ ↭₂ _ _ _) with lemmaA1 b (reverse (ls₁ ++ ls₂))
                                              (trans (sym (length-reverse b)) (trans (↭-length ↭₂) (length-reverse (reverse (ls₁ ++ ls₂)))))
                                              hfr₂
... | ∀₁ = λ f₁ → g₁ f₁
  where g₁ : (f₁ : FileName) -> S.exec s (reverse (x ∷ b)) f₁ ≡ S.exec s (reverse b₁) f₁
        g₁ f₁ = subst₂ (λ x₄ x₅ → S.exec s x₄ f₁ ≡ S.exec s x₅ f₁)
                       (sym (unfold-reverse x b)) (sym reverse-b₁≡ls₁++x∷ls₂)
                       (exec-f₁≡ s f₁ x (reverse b) ls₁ ls₂ ∀₂ ≡₂ all₁ dsj)
                       
          where ∀₂ : (∀ f₂ → S.exec s (reverse b) f₂ ≡ S.exec s (ls₁ ++ ls₂) f₂)
                ∀₂ = subst (λ x₁ → ∀ f₂ → _ ≡ S.exec s x₁ f₂) (reverse-involutive (ls₁ ++ ls₂)) ∀₁
                hf₃ : {xs : List String} (s : System) (x : Cmd) (ls₁ ls₂ : Build) -> HazardFree s (ls₁ ++ x ∷ ls₂) xs -> HazardFree (S.exec s ls₁) (x ∷ ls₂) (S.build-rws s ls₁ xs)
                hf₃ s x [] ls₂ hf = hf
                hf₃ s x (x₁ ∷ ls₁) ls₂ (Cons .x₁ .(ls₁ ++ x ∷ ls₂) _ x₂ hf)
                  = hf₃ (run oracle x₁ s) x ls₁ ls₂ hf
                dsj : Disjoint (S.Cwrites (S.exec s ls₁) x) (writes (run oracle x (S.exec s ls₁)) ls₂)
                dsj = hf→dsj (S.exec s ls₁) x ls₂ (hf₃ s x ls₁ ls₂ (subst (λ x₄ → HazardFree s x₄ _) reverse-b₁≡ls₁++x∷ls₂ hf₂))
                dsj₁ : Disjoint (S.Creads (S.exec s ls₁) x) (writes (S.exec s ls₁) ls₂)
                dsj₁ = still-disjoint (S.exec s ls₁) x ls₂
                       (hfr→dsj s x (reverse b) ls₁ ls₂ hfr₁)
                       (hf→dsj-reads (S.exec s ls₁) x ls₂ (hf₃ s x ls₁ ls₂ (subst (λ x₄ → HazardFree s x₄ _) reverse-b₁≡ls₁++x∷ls₂ hf₂)))
                ≡₂ : proj₁ (oracle x) (S.exec s (reverse b)) ≡ proj₁ (oracle x) (S.exec s ls₁)
                ≡₂ = S.h₄ (S.exec s (reverse b)) (S.exec s ls₁) x (all≡ s (S.Creads (S.exec s ls₁) x) (reverse b) ls₁ ls₂ dsj₁ ∀₂)
                all₁ : All (λ f₂ → S.exec s ls₁ f₂ ≡ run oracle x (S.exec s ls₁) f₂) (S.reads (run oracle x (S.exec s ls₁)) ls₂)
                all₁ = St.lemma5 {S.exec s ls₁} (S.reads (run oracle x (S.exec s ls₁)) ls₂) (proj₂ (proj₁ (oracle x) (S.exec s ls₁))) (hfr→dsj s x (reverse b) ls₁ ls₂ hfr₁)

  
script-reordered : {sys : System} (b b₂ : Build) -> HazardFreeReordering sys b b₂ -> ∀ f₁ → S.exec sys b f₁ ≡ S.exec sys b₂ f₁
script-reordered {sys} b b₂ hfr@(HFR .b .b₂ ↭₁ x₁ x₂ x₃) with lemmaA1 {sys} (reverse b) (reverse b₂) (trans (length-reverse b) (trans (↭-length ↭₁) (sym (length-reverse b₂)))) (subst₂ (λ x x₄ → HazardFreeReordering sys x x₄) (sym (reverse-involutive b)) (sym (reverse-involutive b₂)) hfr) 
... | ∀₁ = subst₂ (λ x x₄ → ∀ f₁ → S.exec sys x f₁ ≡ S.exec sys x₄ f₁) (reverse-involutive b) (reverse-involutive b₂) ∀₁


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

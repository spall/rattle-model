
open import Functional.State as St using (Oracle ; System ; trace ; Cmd ; run ; extend ; inputs ; read ; Memory)

module Functional.Proofs (oracle : Oracle) where

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool

open import Common.List.Properties as CLP using (_before_en_)
open import Functional.Script.Properties (oracle) as FSP

open import Relation.Binary.Definitions using (Decidable)
open import Data.Sum using (_⊎_)
open import Data.Bool as B using (if_then_else_)
open import Data.List using ([] ; List ; _++_ ; _∷_ ; map ; foldr ; _∷ʳ_ ; length ; reverse ; foldl ; [_] ; concatMap)
open import Data.List.Properties using (++-assoc ; unfold-reverse ; ++-identityʳ ; reverse-involutive ; ∷-injective ; length-reverse ; ++-identityˡ)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; ∃-syntax ; _×_ ; Σ-syntax)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-decidable ; ≡×≡⇒≡ ; ≡⇒≡×≡ ; ×-decSetoid)

open import Functional.Build using (Build)
open import Functional.Script.Exec (oracle) as S using (writes)
-- open import Functional.Script.HazardFree (oracle) using (HazardFree ; HazardFreeReordering ; HFR ; Cons ; Null)
-- open import Functional.Script.HazardFree.Properties (oracle) using (hfr-∷ʳ⁻ ; hf→disjointWrites ; hfr→disjoint ; hf→disjointReads)
open import Functional.Forward.Exec (oracle) as Forward hiding (run)
open import Functional.Forward.Properties (oracle) using (run≡ ; IdempotentState ; preserves ; getCmdIdempotent ; cmdReadWrites ; cmdWrites ; ∈-resp-≡ ; cmdReads)
open import Functional.File using (FileName ; Files ; File ; FileContent)
open import Functional.Rattle.Exec (oracle) as Rattle hiding (run)
open import Functional.Rattle.Properties (oracle) using (MemoryProperty ; getProperty ; soundness)
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
open import Data.List.Relation.Unary.All as All using (All ; lookup ; all?)
open import Data.List.Relation.Unary.All.Properties using (¬All⇒Any¬ ; ++⁻ˡ ; ++⁻ʳ)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Maybe using (just ; nothing ; Maybe)
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






-- All (λ f₁ → exec s (reverse b) f₁ ≡ exec s ls₁ f₁) (Creads (exec s ls₁ x))

-- we dont want to prove the writes are equivalent; they might not be the same order, we want to prove theyre the same sets. where order isnt important
lemmaA1 : {sys : System} (b b₁ : Build) -> length b ≡ length b₁ -> HazardFreeReordering sys (reverse b) (reverse b₁) -> ∀ f₁ → S.exec sys (reverse b) f₁ ≡ S.exec sys (reverse b₁) f₁
lemmaA1 {s} [] [] ≡₁ (HFR .[] .[] ↭₁ Null Null ¬swrh) = λ f₁ → refl
lemmaA1 {s} (x ∷ b) b₁ ≡₁ hfr@(HFR _ _ ↭₁ hf₁ hf₂ _) with ∈-∃++ (∈-resp-↭ ↭₁ (reverse⁺ x∈x∷b))
  where x∈x∷b : x ∈ x ∷ b
        x∈x∷b = here refl
... | ls₁ , ls₂ , reverse-b₁≡ls₁++x∷ls₂ with subst₂ (λ x₁ x₂ → HazardFreeReordering s x₁ x₂) (unfold-reverse x b) reverse-b₁≡ls₁++x∷ls₂ hfr
... | hfr₁ with subst (λ x₁ → HazardFreeReordering _ _ x₁) (sym (reverse-involutive (ls₁ ++ ls₂))) (hfr-∷ʳ⁻ {s} x (reverse b) ls₁ ls₂ hfr₁)
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
                hf₃ s x (x₁ ∷ ls₁) ls₂ (Cons _ .x₁ .(ls₁ ++ x ∷ ls₂) x₂ hf)
                  = hf₃ (run oracle x₁ s) x ls₁ ls₂ hf
                dsj : Disjoint (S.Cwrites (S.exec s ls₁) x) (writes (run oracle x (S.exec s ls₁)) ls₂)
                dsj = hf→disjointWrites (S.exec s ls₁) x ls₂ (hf₃ s x ls₁ ls₂ (subst (λ x₄ → HazardFree s x₄ _) reverse-b₁≡ls₁++x∷ls₂ hf₂))
                dsj₁ : Disjoint (S.Creads (S.exec s ls₁) x) (writes (S.exec s ls₁) ls₂)
                dsj₁ = still-disjoint (S.exec s ls₁) x ls₂
                       (hfr→disjoint s x (reverse b) ls₁ ls₂ hfr₁)
                       (hf→disjointReads (S.exec s ls₁) x ls₂ (hf₃ s x ls₁ ls₂ (subst (λ x₄ → HazardFree s x₄ _) reverse-b₁≡ls₁++x∷ls₂ hf₂)))
                ≡₂ : proj₁ (oracle x) (S.exec s (reverse b)) ≡ proj₁ (oracle x) (S.exec s ls₁)
                ≡₂ = S.h₄ (S.exec s (reverse b)) (S.exec s ls₁) x (all≡ s (S.Creads (S.exec s ls₁) x) (reverse b) ls₁ ls₂ dsj₁ ∀₂)
                all₁ : All (λ f₂ → S.exec s ls₁ f₂ ≡ run oracle x (S.exec s ls₁) f₂) (S.reads (run oracle x (S.exec s ls₁)) ls₂)
                all₁ = St.lemma5 {S.exec s ls₁} (S.reads (run oracle x (S.exec s ls₁)) ls₂) (proj₂ (proj₁ (oracle x) (S.exec s ls₁))) (hfr→disjoint s x (reverse b) ls₁ ls₂ hfr₁)

{-
script-reordered : {sys : System} (b b₂ : Build) -> HazardFreeReordering sys b b₂ -> ∀ f₁ → S.exec sys b f₁ ≡ S.exec sys b₂ f₁
script-reordered {sys} b b₂ hfr@(HFR .b .b₂ ↭₁ x₁ x₂ x₃) with lemmaA1 {sys} (reverse b) (reverse b₂) (trans (length-reverse b) (trans (↭-length ↭₁) (sym (length-reverse b₂)))) (subst₂ (λ x x₄ → HazardFreeReordering sys x x₄) (sym (reverse-involutive b)) (sym (reverse-involutive b₂)) hfr) 
... | ∀₁ = subst₂ (λ x x₄ → ∀ f₁ → S.exec sys x f₁ ≡ S.exec sys x₄ f₁) (reverse-involutive b) (reverse-involutive b₂) ∀₁
-}

helper : {sys : System} (ls ls₁ : List Cmd) -> (x : Cmd) -> Disjoint (cmdWrites x sys) ls₁ -> concatMap (λ x₁ → cmdReadWrites x₁ sys) ls ⊆ ls₁ -> All (λ x₁ → Disjoint (cmdWrites x sys) (cmdReadWrites x₁ sys)) ls
helper [] ls₁ x dsj ⊆₁ = All.[]
helper {sys} (x₁ ∷ ls) ls₁ x dsj ⊆₁ = (λ x₂ → dsj ((proj₁ x₂) , ⊆₁ (∈-++⁺ˡ (proj₂ x₂)))) All.∷ (helper ls ls₁ x dsj λ x₂ → ⊆₁ (∈-++⁺ʳ (cmdReadWrites x₁ sys) x₂))

{- This proof requires the hazardfree evidence because the memory does not keep track of whether or not outputs have changed -}
script-exec≡forward-exec : {ls : List String} {sys : System} (b : Build) -> DisjointBuild sys b -> HazardFree sys b ls -> ∀ f₁ → S.exec sys b f₁ ≡ proj₁ (Forward.exec (sys , []) b) f₁
script-exec≡forward-exec {ls} {sys} b dsb hf f₁ = g₁ sys (sys , []) (λ f₂ → refl) b (λ ()) IdempotentState.[] dsb hf

  where g₁ : {ls : List String} (sys₁ : System) ((sys₂ , mm) : St.State) -> (∀ f₁ → sys₁ f₁ ≡ sys₂ f₁) -> (b : Build) -> concatMap (λ x₁ → cmdReadWrites x₁ sys₂) (map proj₁ mm) ⊆ ls -> IdempotentState cmdReads sys₂ mm -> DisjointBuild sys₁ b -> HazardFree sys₁ b ls -> S.exec sys₁ b f₁ ≡ proj₁ (Forward.exec (sys₂ , mm) b) f₁
        g₁ sys₁ (sys₂ , mm) ∀≡₁ [] ⊆₁ is dsb hf = ∀≡₁ f₁
        g₁ {ls} sys₁ (sys₂ , mm) ∀≡₁ (x ∷ b) ⊆₁ is (Cons .x ds .b dsb) (Cons _ .x .b dsj hf) with x ∈? map proj₁ mm
        ... | no x∉ = g₁ (run oracle x sys₁) (Forward.doRun (sys₂ , mm) x) (λ f₂ → St.lemma2 {oracle} {sys₁} {sys₂} x f₂ (proj₂ (oracle x) sys₁ sys₂ λ f₃ _ → ∀≡₁ f₃) (∀≡₁ f₂)) b ⊆₂
                         (preserves {sys₂} {mm} x (λ x₂ → ds (subst (λ x₃ → _ ∈ map proj₁ (proj₁ x₃)) ≡₁ (proj₁ x₂) , subst (λ x₃ → _ ∈ map proj₁ (proj₂ x₃)) ≡₁ (proj₂ x₂))) all₁ is) dsb hf
                         
                           where ≡₁ : proj₁ (oracle x) sys₂ ≡ proj₁ (oracle x) sys₁
                                 ≡₁ = proj₂ (oracle x) sys₂ sys₁ λ f₂ _ → sym (∀≡₁ f₂)
                                 
                                 ≡₅ : (x₁ : Cmd) -> Disjoint (cmdWrites x sys₂) (cmdReadWrites x₁ sys₂) -> proj₁ (oracle x₁) (run oracle x sys₂) ≡ proj₁ (oracle x₁) sys₂
                                 ≡₅ x₁ ds = sym (proj₂ (oracle x₁) sys₂ (St.run oracle x sys₂) λ f₂ x₂ → St.lemma3 f₂ (proj₂ (proj₁ (oracle x) sys₂)) λ x₃ → ds (x₃ , ∈-++⁺ˡ x₂))

                                 ≡₄ : proj₁ (oracle x) (run oracle x sys₂) ≡ proj₁ (oracle x) sys₁
                                 ≡₄ = trans (sym (proj₂ (oracle x) sys₂ (St.run oracle x sys₂) λ f₂ x₁ → (St.lemma3 f₂ (proj₂ (proj₁ (oracle x) sys₂)) λ x₂ → ds (∈-resp-≡ x₁ (cong (map proj₁ ∘ proj₁) ≡₁) , ∈-resp-≡ x₂ (cong (map proj₁ ∘ proj₂) ≡₁))))) ≡₁
                                 ≡₂ : cmdReadWrites x (run oracle x sys₂) ≡ cmdReadWrites x sys₁
                                 ≡₂ = cong₂ _++_ (cong (map proj₁ ∘ proj₁) ≡₄) (cong (map proj₁ ∘ proj₂) ≡₄)
                                 ≡₃ : (ls : List String) -> All (λ x₂ → Disjoint (cmdWrites x sys₂) (cmdReadWrites x₂ sys₂)) ls -> concatMap (λ x₁ → cmdReadWrites x₁ (St.run oracle x sys₂)) ls ≡ concatMap (λ x₁ → cmdReadWrites x₁ sys₂) ls
                                 ≡₃ [] all₁ = refl
                                 ≡₃ (y ∷ ls) (px All.∷ all₁) = cong₂ _++_ (cong₂ _++_ (cong (map proj₁ ∘ proj₁) (≡₅ y px)) (cong (map proj₁ ∘ proj₂) (≡₅ y px))) (≡₃ ls all₁)
                                 all₁ : All (λ x₂ → Disjoint (cmdWrites x sys₂) (cmdReadWrites x₂ sys₂)) (map proj₁ mm)
                                 all₁ = helper (map proj₁ mm) ls x (λ x₂ → dsj (subst (λ x₁ → _ ∈ map proj₁ (proj₂ x₁)) ≡₁ (proj₁ x₂) , (proj₂ x₂))) ⊆₁
                                 ⊆₂ : concatMap (λ x₁ → cmdReadWrites x₁ (St.run oracle x sys₂)) (x ∷ map proj₁ mm) ⊆ (cmdReadWrites x sys₁) ++ ls
                                 ⊆₂ x₂ with ∈-++⁻ (cmdReadWrites x (run oracle x sys₂)) x₂
                                 ... | inj₁ ∈₁ = ∈-++⁺ˡ (subst (λ x₃ → _ ∈ x₃) ≡₂ ∈₁)
                                 ... | inj₂ ∈₂ = ∈-++⁺ʳ _ (⊆₁ (subst (λ x₃ → _ ∈ x₃) (≡₃ (map proj₁ mm) all₁) ∈₂))
                                 
        ... | yes x∈ with maybeAll {sys₂} (get x mm x∈)
        ... | nothing = g₁ (run oracle x sys₁) (Forward.doRun (sys₂ , mm) x) (λ f₂ → St.lemma2 {oracle} {sys₁} {sys₂} x f₂ (proj₂ (oracle x) sys₁ sys₂ λ f₃ _ → ∀≡₁ f₃) (∀≡₁ f₂)) b ⊆₂
                         (preserves {sys₂} {mm} x (λ x₂ → ds (subst (λ x₃ → _ ∈ map proj₁ (proj₁ x₃)) ≡₁ (proj₁ x₂) , subst (λ x₃ → _ ∈ map proj₁ (proj₂ x₃)) ≡₁ (proj₂ x₂))) all₁ is) dsb hf
                         
                           where ≡₁ : proj₁ (oracle x) sys₂ ≡ proj₁ (oracle x) sys₁
                                 ≡₁ = proj₂ (oracle x) sys₂ sys₁ λ f₂ _ → sym (∀≡₁ f₂)
                                 
                                 ≡₅ : (x₁ : Cmd) -> Disjoint (cmdWrites x sys₂) (cmdReadWrites x₁ sys₂) -> proj₁ (oracle x₁) (run oracle x sys₂) ≡ proj₁ (oracle x₁) sys₂
                                 ≡₅ x₁ ds = sym (proj₂ (oracle x₁) sys₂ (St.run oracle x sys₂) λ f₂ x₂ → St.lemma3 f₂ (proj₂ (proj₁ (oracle x) sys₂)) λ x₃ → ds (x₃ , ∈-++⁺ˡ x₂))

                                 ≡₄ : proj₁ (oracle x) (run oracle x sys₂) ≡ proj₁ (oracle x) sys₁
                                 ≡₄ = trans (sym (proj₂ (oracle x) sys₂ (St.run oracle x sys₂) λ f₂ x₁ → (St.lemma3 f₂ (proj₂ (proj₁ (oracle x) sys₂)) λ x₂ → ds (∈-resp-≡ x₁ (cong (map proj₁ ∘ proj₁) ≡₁) , ∈-resp-≡ x₂ (cong (map proj₁ ∘ proj₂) ≡₁))))) ≡₁
                                 ≡₂ : cmdReadWrites x (run oracle x sys₂) ≡ cmdReadWrites x sys₁
                                 ≡₂ = cong₂ _++_ (cong (map proj₁ ∘ proj₁) ≡₄) (cong (map proj₁ ∘ proj₂) ≡₄)
                                 ≡₃ : (ls : List String) -> All (λ x₂ → Disjoint (cmdWrites x sys₂) (cmdReadWrites x₂ sys₂)) ls -> concatMap (λ x₁ → cmdReadWrites x₁ (St.run oracle x sys₂)) ls ≡ concatMap (λ x₁ → cmdReadWrites x₁ sys₂) ls
                                 ≡₃ [] all₁ = refl
                                 ≡₃ (y ∷ ls) (px All.∷ all₁) = cong₂ _++_ (cong₂ _++_ (cong (map proj₁ ∘ proj₁) (≡₅ y px)) (cong (map proj₁ ∘ proj₂) (≡₅ y px))) (≡₃ ls all₁)
                                 all₁ : All (λ x₂ → Disjoint (cmdWrites x sys₂) (cmdReadWrites x₂ sys₂)) (map proj₁ mm)
                                 all₁ = helper (map proj₁ mm) ls x (λ x₂ → dsj (subst (λ x₁ → _ ∈ map proj₁ (proj₂ x₁)) ≡₁ (proj₁ x₂) , (proj₂ x₂))) ⊆₁
                                 ⊆₂ : concatMap (λ x₁ → cmdReadWrites x₁ (St.run oracle x sys₂)) (x ∷ map proj₁ mm) ⊆ (cmdReadWrites x sys₁) ++ ls
                                 ⊆₂ x₂ with ∈-++⁻ (cmdReadWrites x (run oracle x sys₂)) x₂
                                 ... | inj₁ ∈₁ = ∈-++⁺ˡ (subst (λ x₃ → _ ∈ x₃) ≡₂ ∈₁)
                                 ... | inj₂ ∈₂ = ∈-++⁺ʳ _ (⊆₁ (subst (λ x₃ → _ ∈ x₃) (≡₃ (map proj₁ mm) all₁) ∈₂))
                                 
        ... | just all₁ with getCmdIdempotent mm x is x∈
        ... | ci = g₁ (St.run oracle x sys₁) (sys₂ , mm) (λ f₂ → trans (St.lemma2 {oracle} {sys₁} {sys₂} x f₂ (proj₂ (oracle x) sys₁ sys₂ λ f₃ _ → ∀≡₁ f₃) (∀≡₁ f₂))
                                                                        (ci all₁ f₂)) b (λ x₁ → ∈-++⁺ʳ _ (⊆₁ x₁)) is dsb hf

forward-reordered : {sys : System} (b : Build) -> (b₂ : Build) -> DisjointBuild sys b -> DisjointBuild sys b₂ -> HazardFreeReordering sys b b₂ -> ∀ f₁ → proj₁ (Forward.exec (sys , []) b) f₁ ≡ proj₁ (Forward.exec (sys , []) b₂) f₁
forward-reordered {sys} b b₂ ds ds₂ hfr@(HFR .b .b₂ _ hf₁ hf₂ _)
  = λ f₁ → trans (sym (script-exec≡forward-exec b ds hf₁ f₁)) (trans (script-reordered b b₂ hfr f₁) (script-exec≡forward-exec b₂ ds₂ hf₂ f₁))

{- This proof does not require the hazardfree evidence because the memory does record the values of outputs -}
script-exec≡rattle-exec : {sys : System} (b : Build) -> DisjointBuild sys b -> ∀ f₁ → S.exec sys b f₁ ≡ proj₁ (Rattle.exec (sys , []) b) f₁
script-exec≡rattle-exec {sys} b ds f₁ = g₁ sys (sys , []) (λ f₂ → refl) b ds MemoryProperty.[]
  where g₁ : (sys₁ : System) ((sys₂ , mm) : St.State) -> (∀ f₁ → sys₁ f₁ ≡ sys₂ f₁) -> (b : Build) -> DisjointBuild sys₁ b -> MemoryProperty mm -> S.exec sys₁ b f₁ ≡ proj₁ (Rattle.exec (sys₂ , mm) b) f₁
        g₁ sys₁ (sys₂ , mm) ∀≡₁ [] ds mp = ∀≡₁ f₁
        g₁ sys₁ (sys₂ , mm) ∀≡₁ (x ∷ b) (Cons .x ds .b dsb) mp with x ∈? map proj₁ mm
        ... | no x∉ = g₁ (run oracle x sys₁) (Rattle.doRun (sys₂ , mm) x) (λ f₂ → St.lemma2 {oracle} {sys₁} {sys₂} x f₂ (proj₂ (oracle x) sys₁ sys₂ λ f₃ _ → ∀≡₁ f₃) (∀≡₁ f₂)) b dsb (MemoryProperty.Cons x sys₂ (λ f₂ x₁ → St.lemma3 f₂ (proj₂ (proj₁ (oracle x) sys₂)) λ x₂ → ds (∈-resp-≡ x₁ (cong (map proj₁ ∘ proj₁) ≡₁) , ∈-resp-≡ x₂ (cong (map proj₁ ∘ proj₂) ≡₁))) mp)
          where ≡₁ : proj₁ (oracle x) sys₂ ≡ proj₁ (oracle x) sys₁
                ≡₁ = proj₂ (oracle x) sys₂ sys₁ λ f₂ x₁ → sym (∀≡₁ f₂)
        ... | yes x∈ with maybeAll {sys₂} (get x mm x∈)
        ... | nothing = g₁ (run oracle x sys₁) (Rattle.doRun (sys₂ , mm) x) (λ f₂ → St.lemma2 {oracle} {sys₁} {sys₂} x f₂ (proj₂ (oracle x) sys₁ sys₂ λ f₃ _ → ∀≡₁ f₃) (∀≡₁ f₂)) b dsb (MemoryProperty.Cons x sys₂ (λ f₂ x₁ → St.lemma3 f₂ (proj₂ (proj₁ (oracle x) sys₂)) λ x₂ → ds (∈-resp-≡ x₁ (cong (map proj₁ ∘ proj₁) ≡₁) , ∈-resp-≡ x₂ (cong (map proj₁ ∘ proj₂) ≡₁))) mp)
          where ≡₁ : proj₁ (oracle x) sys₂ ≡ proj₁ (oracle x) sys₁
                ≡₁ = proj₂ (oracle x) sys₂ sys₁ λ f₂ x₁ → sym (∀≡₁ f₂) 
        ... | just all₁ with getProperty x mp x∈
        ... | sys₃ , get≡ , ∀≡₂ = g₁ (St.run oracle x sys₁) (sys₂ , mm) (λ f₂ → ≡ₓ) b dsb mp
          where all₂ : (ls : List (FileName × Maybe FileContent)) (ls₁ : List FileName) -> All (λ (f₁ , v₁) → sys₂ f₁ ≡ v₁) ls -> ls ≡ map (λ f₁ → f₁ , St.run oracle x sys₃ f₁) ls₁ -> All (λ f₁ → sys₂ f₁ ≡ St.run oracle x sys₃ f₁) ls₁
                all₂ ls [] all₁ ≡₁ = All.[]
                all₂ (_ ∷ ls) (x ∷ ls₁) (px All.∷ all₁) ≡₁ with ∷-injective ≡₁
                ... | _≡x , ls≡ = (trans (cong (sys₂ ∘ proj₁) (sym _≡x)) (trans px (cong proj₂ _≡x))) All.∷ (all₂ ls ls₁ all₁ ls≡)
                
                ≡₀ : proj₁ (oracle x) sys₂ ≡ proj₁ (oracle x) sys₃ 
                ≡₀ = sym (proj₂ (oracle x) sys₃ sys₂ λ f₂ x₁ → trans (∀≡₂ f₂ x₁) (sym (lookup (all₂ (get x mm x∈) (cmdReadWrites x sys₃) all₁ get≡) (∈-++⁺ˡ x₁))))
                
                ≡₁ : (f₁ : FileName) -> f₁ ∈ cmdWrites x sys₂ -> St.run oracle x sys₂ f₁ ≡ St.run oracle x sys₃ f₁
                ≡₁ f₁ f₁∈ = subst (λ x₁ → foldr extend sys₂ (proj₂ (proj₁ (oracle x) sys₂)) f₁ ≡ foldr extend sys₃ x₁ f₁) (cong proj₂ ≡₀) (St.lemma4 {sys₂} {sys₃} (proj₂ (proj₁ (oracle x) sys₂)) f₁ f₁∈)
                ≡₂ : (f₁ : FileName) -> f₁ ∈ cmdWrites x sys₂ -> St.run oracle x sys₃ f₁ ≡ sys₂ f₁
                ≡₂ f₁ f₁∈ = sym (lookup (all₂ (get x mm x∈) (cmdReadWrites x sys₃) all₁ get≡) (∈-++⁺ʳ _ (∈-resp-≡ f₁∈ (cong (map proj₁ ∘ proj₂) ≡₀))))
                ≡ₓ : {f₁ : FileName} -> St.run oracle x sys₁ f₁ ≡ sys₂ f₁
                ≡ₓ with _ ∈? cmdWrites x sys₂
                ... | no _∉ = trans (St.lemma2 {oracle} {sys₁} {sys₂} x _ (proj₂ (oracle x) sys₁ sys₂ λ f₂ x₁ → ∀≡₁ f₂) (∀≡₁ _)) (sym (St.lemma3 _ (proj₂ (proj₁ (oracle x) sys₂)) _∉))
                ... | yes _∈ = trans (St.lemma2 {oracle} {sys₁} {sys₂} x _ (proj₂ (oracle x) sys₁ sys₂ λ f₂ x₁ → ∀≡₁ f₂) (∀≡₁ _))
                                     (trans (≡₁ _ _∈) (≡₂ _ _∈))


rattle-reordered : {sys : System} (b : Build) -> (b₂ : Build) -> DisjointBuild sys b -> DisjointBuild sys b₂ -> HazardFreeReordering sys b b₂ -> ∀ f₁ → proj₁ (Rattle.exec (sys , []) b) f₁ ≡ proj₁ (Rattle.exec (sys , []) b₂) f₁
rattle-reordered b b₂ ds ds₂ hfr@(HFR .b .b₂ x x₁ x₂ x₃)
  = λ f₁ → trans (sym (script-exec≡rattle-exec b ds f₁)) (trans (script-reordered b b₂ hfr f₁) (script-exec≡rattle-exec b₂ ds₂ f₁))

{-
-- does rattle ever give the wrong answer?
soundness2 : {sys sys₁ : System} {fi fi₁ : FileInfo} {b₁ : Build} (b : Build) -> DisjointBuild sys b -> execWError ((sys , []) , fi) b b₁ ≡ inj₂ ((sys₁ , _) , fi₁) -> ∀ f₁ → S.exec sys b f₁ ≡ sys₁ f₁
soundness2 {sys} {sys₁} {fi} b dsj ≡₁ f₁ = trans (script-exec≡rattle-exec b dsj f₁) (cong-app (cong proj₁ (soundness b ≡₁)) f₁)\
-}

{- 1. produce an error ; completeness says that for a build with no hazards 
      behaves the same whether or not we check for errors; 
      which means it cannot produce errors . 
   2. behave like script; behaves like script if it doesn't produce an error.
   3. behave some other way ; aka this is not possible. 
-}

-- correctness: HazardFree build →  you get the same execution as the script using executing with errors version of rattle
-- use soundness and completeness to prove it. 


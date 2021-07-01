{-# OPTIONS --allow-unsolved-metas #-}
open import Functional.State as St using (F ; System ; Memory ; Cmd ; trace ; extend ; State)

module Functional.Rattle.Properties (oracle : F) where

open import Agda.Builtin.Equality

open import Common.List.Properties using (∈-resp-≡ ; l11)
open import Functional.Forward.Properties (oracle) using (cmdWrites ; cmdReadWrites ; IdempotentState ; IdempotentCmd ; cmdIdempotent ; cmdReads)
open import Functional.Forward.Exec (oracle) using (get ; maybeAll ; run?)
open import Functional.File using (FileName ; FileContent)
open import Data.Bool using (true ; false ; if_then_else_)

open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∃-syntax)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Data.List using (List ; map ; _++_ ; foldr ; _∷_ ; [] ; concatMap ; reverse)
open import Data.List.Properties using (∷-injective ; unfold-reverse)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Relation.Binary.PropositionalEquality using (trans ; cong ; cong-app ; sym ; decSetoid ; cong₂ ; subst ; inspect ; [_])
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-++⁻)
open import Function.Base using (_∘_)
open import Data.String.Properties using (_≟_ ; _==_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Unary.Any using (tail)
open import Functional.Rattle.Exec (oracle) using (execWError ; runWError ; run ; doRunCheck ; doRun ; checkWriteRead ; hasHazard ; exec)
open import Functional.Build using (Build)
open import Data.Sum using (inj₂ ; from-inj₂ ; inj₁ )
open import Data.Sum.Properties using (inj₂-injective)
open import Functional.Script.Exec (oracle) as Script hiding (exec)
open import Functional.Script.HazardFree (oracle) using (HazardFree ; Cons ; SpeculativeWRHazard ; WriteBeforeRead)
open import Functional.Script.HazardFree.Properties (oracle) using (hf-∷⁻-∀)
open import Functional.Script.Properties (oracle) using (DisjointBuild)
open import Functional.Rattle.Hazard (oracle) using (Hazard ; ReadWrite ; WriteWrite ; SpeculativeWriteRead ; FileInfo ; readsWrites ; ran)


data MemoryProperty : Memory -> Set where
 []   : MemoryProperty []
 Cons : {mm : Memory} (x : Cmd) -> (sys : System) -> (∀ f₁ → f₁ ∈ cmdReads x sys -> sys f₁ ≡ St.run oracle x sys f₁) -> MemoryProperty mm -> MemoryProperty ((x , map (λ f₁ → f₁ , (St.run oracle x sys) f₁) (cmdReadWrites x sys)) ∷ mm)

getProperty : {mm : Memory} (x : Cmd) -> MemoryProperty mm -> (x∈ : x ∈ map proj₁ mm) -> ∃[ sys ](get x mm x∈ ≡ map (λ f₁ → f₁ , (St.run oracle x sys) f₁) (cmdReadWrites x sys) × ∀ f₁ → f₁ ∈ cmdReads x sys -> sys f₁ ≡ St.run oracle x sys f₁)
getProperty x (Cons x₁ sys ∀₁ mp) x∈ with x ≟ x₁
... | yes x≡x₁ = sys , cong (λ x₂ → map (λ f₁ → f₁ , foldr extend sys (proj₂ (proj₁ (oracle x₂) sys)) f₁) (cmdReadWrites x₂ sys)) (sym x≡x₁) , λ f₁ x₂ → subst (λ x₃ → sys f₁ ≡ St.run oracle x₃ sys f₁) (sym x≡x₁) (∀₁ f₁ (subst (λ x₃ → f₁ ∈ map proj₁ (proj₁ (proj₁ (oracle x₃) sys))) x≡x₁ x₂))
... | no ¬x≡x₁ = getProperty x mp (tail ¬x≡x₁ x∈)

{-
doRunSoundness : {sys₀ : System} {st st₁ : State} {b rf : Build} {fi : FileInfo sys₀ b} (x : Cmd) {fi₁ : FileInfo sys₀ (b ++ x ∷ [])} -> doRunCheck st fi x rf ≡ inj₂ (st₁ , fi₁) -> doRun st x ≡ st₁
doRunSoundness {sys₀} {st} {st₁} {b} {rf} {fi} x {fi₁} ≡₁ with hasHazard st fi x rf
... | nothing = cong proj₁ (inj₂-injective ≡₁)


runSoundness : {sys₀ : System} {st st₁ : State} {b rf : Build} {fi : FileInfo sys₀ b} (x : Cmd) {fi₁ : FileInfo sys₀ (b ++ x ∷ [])} -> runWError st fi x rf ≡ inj₂ (st₁ , fi₁) -> run st x ≡ st₁
runSoundness {sys₀} {st} {st₁} {b} {rf} {fi} x {fi₁} ≡₁ with run? x st
... | true = doRunSoundness {sys₀} {st} {st₁} {b} {rf} {fi} x {fi₁} {!!}
... | false = cong proj₁ (inj₂-injective ≡₁)

soundness : {sys₀ : System} {st st₁ : State} {b₁ b₂ rf : Build} {fi : FileInfo sys₀ b₁} {fi₁ : FileInfo sys₀ b₂} {rf : Build} (b : Build) -> execWError (st , fi) b rf ≡ inj₂ (b₂ , st₁ , fi₁) -> exec st b ≡ st₁
soundness [] ≡₁ = cong proj₁ (inj₂-injective {!!})
soundness {sys₀} {st} {st₁} {b₁} {b₂} {rf} {fi} {fi₁} (x ∷ b) ≡₁ with runWError st fi x rf | inspect (runWError st fi x) rf
... | inj₂ (st₂ , fi₂) | [ ≡₂ ] with run? x st | runSoundness {sys₀} {st} {st₂} {b₁} {rf} {fi} x {fi₂} ≡₂
... | false | st≡st₂ = soundness b (subst (λ x₁ → execWError (x₁ , fi₂) b rf ≡ _) (sym st≡st₂) {!!})
... | true | ≡₃ = soundness b (subst (λ x₁ → execWError (x₁ , fi₂) b rf ≡ _) (sym ≡₃) {!!})
-}


-- runWError ≡ run if runWError ≡ inj₂

-- prove if no errors ; do run and dorun check are the same ; aka give same system

-- completeness, does rattle actually work for pieces of software?


g₁ : (f₁ : FileName) (ls : List (FileName × (List FileName × List FileName))) -> f₁ ∈ concatMap (proj₁ ∘ proj₂) ls -> f₁ ∈ concatMap (\x -> (proj₁ (proj₂ x)) ++ (proj₂ (proj₂ x))) ls
g₁ f₁ ((_ , ls₁ , ls₂) ∷ ls) f₁∈ls with f₁ ∈? ls₁
... | yes f₁∈ls₁ = ∈-++⁺ˡ (∈-++⁺ˡ f₁∈ls₁)
... | no f₁∉ls₁ with ∈-++⁻ ls₁ f₁∈ls
... | inj₁ f₁∈ls₁ = contradiction f₁∈ls₁ f₁∉ls₁
... | inj₂ f₁∈rest = ∈-++⁺ʳ (ls₁ ++ ls₂) (g₁ f₁ ls f₁∈rest)

g₂ : (f₁ : FileName) (ls : List (FileName × (List FileName × List FileName))) -> f₁ ∈ concatMap (proj₂ ∘ proj₂) ls -> f₁ ∈ concatMap (\x -> (proj₁ (proj₂ x)) ++ (proj₂ (proj₂ x))) ls
g₂ f₁ ((_ , ls₁ , ls₂) ∷ ls) f₁∈ls with f₁ ∈? ls₂
... | yes f₁∈ls₂ = ∈-++⁺ˡ (∈-++⁺ʳ ls₁ f₁∈ls₂)
... | no f₁∉ls₂ with ∈-++⁻ ls₂ f₁∈ls
... | inj₁ f₁∈ls₂ = contradiction f₁∈ls₂ f₁∉ls₂
... | inj₂ f₁∈rest = ∈-++⁺ʳ (ls₁ ++ ls₂) (g₂ f₁ ls f₁∈rest)
{-
doRunCheckCompleteness : {st@(sys , mm) : State} {fi : FileInfo} {b : Build} (x : Cmd) -> Disjoint (cmdWrites x sys) (concatMap (\x -> (proj₁ (proj₂ x)) ++ (proj₂ (proj₂ x))) fi) -> ∃[ st₁ ](∃[ fi₁ ](doRunCheck st fi x b ≡ inj₂ (st₁ , fi₁)))
doRunCheckCompleteness {st@(sys , mm)} {fi} {rf} x dsj with hasHazard st fi x rf
... | nothing = (doRun st x) , (x , proj₁ (trace oracle sys x) , (proj₂ (trace oracle sys x))) ∷ fi , refl
... | just (ReadWrite f₁ ∈₁ ∈₂) = contradiction (∈₁ , g₁ f₁ fi ∈₂) dsj
... | just (WriteWrite f₁ ∈₁ ∈₂) = contradiction (∈₁ , g₂ f₁ fi ∈₂) dsj
... | just (SpeculativeWriteRead a b c d)  = contradiction {!!} {!!}

runWErrorCompleteness : {st@(sys , mm) : State} {fi : FileInfo} {rf : Build} (x : Cmd) -> Disjoint (cmdWrites x sys) (concatMap (\x -> (proj₁ (proj₂ x)) ++ (proj₂ (proj₂ x))) fi)-> ∃[ st₁ ](∃[ fi₁ ](runWError st fi x rf ≡ inj₂ (st₁ , fi₁)))
runWErrorCompleteness {st} {fi} {rf} x dsj with run? x st
... | false = st , fi , refl
... | true = doRunCheckCompleteness {st} {fi} {rf} x dsj
-}
-- completeness2 : {sys : System} {mm : Memory} {fi : FileInfo} {rf : Build} {hz : Hazard} (b : Build) -> execWError ((sys , mm) , fi) b rf ≡ inj₁ hz -> {!!}

-- write a definition that is has a hazard inductively ; opposite of hazardfree def ; then could get rid of negation

wbr-∷ : {sys : System} {x₀ x₁ : Cmd} {b : Build} (x : Cmd) -> WriteBeforeRead (St.run oracle x sys) x₁ x₀ b -> WriteBeforeRead sys x₁ x₀ (x ∷ b)
wbr-∷ x (f₁ , xs , ys , zs , ≡₁ , ∈writes , ∈reads)
  = f₁ , (x ∷ xs) , ys , zs , cong (x ∷_) ≡₁ , ∈writes , ∈reads



wbr-∷₂ : {sys : System} {x₀ x₁ : Cmd} {b : Build} (x : Cmd) -> (∀ f₁ → sys f₁ ≡ St.run oracle x sys f₁) -> WriteBeforeRead sys x₁ x₀ b -> WriteBeforeRead sys x₁ x₀ (x ∷ b)
wbr-∷₂ {sys} {x₀} {x₁} x ∀₁ (f₁ , xs , ys , zs , ≡₁ , ∈writes , ∈reads)
  = f₁ , x ∷ xs , ys , zs , cong (x ∷_) ≡₁ , ∈-resp-≡ f₁ (cmdWrites x₁ (Script.exec sys xs)) (cmdWrites x₁ (Script.exec sys (x ∷ xs))) (cong (map proj₁ ∘ proj₂) ≡₂) ∈writes
  , ∈-resp-≡ f₁ (cmdReads x₀ (Script.exec sys (xs ++ x₁ ∷ ys))) (cmdReads x₀ (Script.exec sys (x ∷ xs ++ x₁ ∷ ys))) (cong (map proj₁ ∘ proj₁) ≡₃) ∈reads
    where ∀≡ : {sys₁ sys₂ : System} (ls : Build) -> (∀ f₁ → sys₁ f₁ ≡ sys₂ f₁) -> ∀ f₁ → Script.exec sys₁ ls f₁ ≡ Script.exec sys₂ ls f₁
          ∀≡ [] ∀₁ = ∀₁
          ∀≡ {sys₁} {sys₂} (x ∷ ls) ∀₁ = ∀≡ ls λ f₂ → St.lemma2 {oracle} x f₂ (proj₂ (oracle x) sys₁ sys₂ λ f₃ _ → ∀₁ f₃) (∀₁ f₂)
          ≡₂ : proj₁ (oracle x₁) (Script.exec sys xs) ≡ proj₁ (oracle x₁) (Script.exec sys (x ∷ xs))
          ≡₂ = proj₂ (oracle x₁) (Script.exec sys xs) (Script.exec sys (x ∷ xs)) λ f₂ x₂ → ∀≡ xs ∀₁ f₂
          ≡₃ : proj₁ (oracle x₀) (Script.exec sys (xs ++ x₁ ∷ ys)) ≡ proj₁ (oracle x₀) (Script.exec sys (x ∷ xs ++ x₁ ∷ ys))
          ≡₃ = proj₂ (oracle x₀) (Script.exec sys (xs ++ x₁ ∷ ys)) (Script.exec sys (x ∷ xs ++ x₁ ∷ ys)) λ f₂ x₂ → ∀≡ (xs ++ x₁ ∷ ys) ∀₁ f₂


lemma1 : {sys : System} {rf : Build} {x : Cmd} {b : Build} -> ¬ SpeculativeWRHazard sys rf (x ∷ b) -> ¬ SpeculativeWRHazard (St.run oracle x sys) rf b
lemma1 {sys} {rf} {x} {b} ¬swrh = λ x₁ → ¬swrh (g₃ x₁)
  where g₃ : SpeculativeWRHazard (St.run oracle x sys) rf b -> SpeculativeWRHazard sys rf (x ∷ b) 
        g₃ (x₀ , x₂ , wbr , before) = x₀ , x₂ , wbr-∷ x wbr , before

lemma2 : {sys : System} {rf b : Build} {x : Cmd} -> (∀ f₁ → sys f₁ ≡ St.run oracle x sys f₁) -> ¬ SpeculativeWRHazard sys rf (x ∷ b) -> ¬ SpeculativeWRHazard sys rf b
lemma2 {sys} {rf} {b} {x} ∀₁ ¬swrh = λ x₁ → ¬swrh (g₃ x₁)
  where g₃ : SpeculativeWRHazard sys rf b -> SpeculativeWRHazard sys rf (x ∷ b)
        g₃ (x₀ , x₁ , wbr , before) = x₀ , x₁ , wbr-∷₂ x ∀₁ wbr , before

wbr-insert : {sys : System} {x₂ x₁ x : Cmd} (b₁ b : Build) -> (∀ f₁ → Script.exec sys b₁ f₁ ≡ St.run oracle x (Script.exec sys b₁) f₁) -> WriteBeforeRead sys x₂ x₁ (b₁ ++ b) -> WriteBeforeRead sys x₂ x₁ (b₁ ++ x ∷ b)
wbr-insert {sys} {x₂} {x₁} {x} [] b ∀₁ (f₁ , xs , ys , zs , ≡₁ , f₁∈writes , f₁∈reads)
  = f₁ , x ∷ xs , ys , zs , cong (x ∷_) ≡₁ , ∈-resp-≡ f₁ (cmdWrites x₂ (Script.exec sys xs)) (cmdWrites x₂ (Script.exec sys (x ∷ xs))) (cong (map proj₁ ∘ proj₂) ≡₃) f₁∈writes , ∈-resp-≡ f₁ (cmdReads x₁ (Script.exec sys (xs ++ x₂ ∷ ys))) (cmdReads x₁ (Script.exec sys (x ∷ xs ++ x₂ ∷ ys))) (cong (map proj₁ ∘ proj₁) ≡₂) f₁∈reads
    where ≡₂ : proj₁ (oracle x₁) (Script.exec sys (xs ++ x₂ ∷ ys)) ≡ proj₁ (oracle x₁) (Script.exec sys (x ∷ xs ++ x₂ ∷ ys))
          ≡₂ = proj₂ (oracle x₁) (Script.exec sys (xs ++ x₂ ∷ ys)) (Script.exec sys (x ∷ xs ++ x₂ ∷ ys)) λ f₂ x₃ → exec-≡ (xs ++ x₂ ∷ ys) ∀₁ f₂
          ≡₃ : proj₁ (oracle x₂) (Script.exec sys xs) ≡ proj₁ (oracle x₂) (Script.exec sys (x ∷ xs))
          ≡₃ = proj₂ (oracle x₂) (Script.exec sys xs) (Script.exec sys (x ∷ xs)) λ f₂ x₃ → exec-≡ xs ∀₁ f₂
wbr-insert {sys} {x₂} {x₁} (x ∷ b₁) b ∀₁ (f₁ , [] , ys , zs , ≡₁ , f₁∈writes , f₁∈reads) with ∷-injective ≡₁
... | x≡x₂ , ≡₂ with g₃ _ _ b₁ b ys zs ∀₁ (subst (λ x₃ → f₁ ∈ cmdReads x₁ (Script.exec (St.run oracle x₃ sys) ys)) (sym x≡x₂) f₁∈reads) ≡₂ 
  where g₃ : {sys : System} (b d : Cmd) -> (as bs cs ds : Build) -> (∀ f₁ → Script.exec sys as f₁ ≡ St.run oracle b (Script.exec sys as) f₁) -> f₁ ∈ cmdReads d (Script.exec sys cs) -> as ++ bs ≡ cs ++ d ∷ ds -> ∃[ es ](∃[ fs ](as ++ b ∷ bs ≡ es ++ d ∷ fs × f₁ ∈ cmdReads d (Script.exec sys es)))
        g₃ {sys} b d [] bs cs ds ∀₁ f₁∈ ≡₁
          = (b ∷ cs) , ds , cong (b ∷_) ≡₁ , ∈-resp-≡ f₁ (cmdReads d (Script.exec sys cs)) (cmdReads d (Script.exec sys (b ∷ cs))) ≡₃ f₁∈
          where ≡₃ : cmdReads d (Script.exec sys cs) ≡ cmdReads d (Script.exec (St.run oracle b sys) cs)
                ≡₃ = cong (map proj₁ ∘ proj₁) (proj₂ (oracle d) (Script.exec sys cs) (Script.exec (St.run oracle b sys) cs) λ f₂ x₄ → exec-≡ cs ∀₁ f₂)
                
        g₃ b d (x ∷ as) bs [] ds ∀₁ f₁∈ ≡₁ with ∷-injective ≡₁
        ... | x≡d , ≡₂ = [] , as ++ b ∷ bs , cong (_∷ (as ++ b ∷ bs)) x≡d , f₁∈
        
        g₃ {sys} b d (x ∷ as) bs (x₁ ∷ cs) ds ∀₁ f₁∈ ≡₁ with ∷-injective ≡₁
        ... | x≡x₁ , ≡₂ with g₃ b d as bs cs ds ∀₁ (subst (λ x₄ → f₁ ∈ cmdReads d (Script.exec sys (x₄ ∷ cs))) (sym x≡x₁) f₁∈) ≡₂
        ... | es , fs , ≡₃ , f₁∈₂ = x₁ ∷ es , fs , cong₂ _∷_ x≡x₁ ≡₃ , subst (λ x₄ → f₁ ∈ cmdReads d (Script.exec (St.run oracle x₄ sys) es)) x≡x₁ f₁∈₂
... | (as , bs , ≡₃ , f₁∈reads₂) = f₁ , [] , as , bs , cong₂ _∷_ x≡x₂ ≡₃ , f₁∈writes , subst (λ x₃ → f₁ ∈ cmdReads x₁ (Script.exec (St.run oracle x₃ sys) as)) x≡x₂ f₁∈reads₂
  
wbr-insert {sys} (x ∷ b₁) b ∀₁ (f₁ , x₁ ∷ xs , ys , zs , ≡₁ , f₁∈writes , f₁∈reads) with ∷-injective ≡₁
... | x≡x₁ , ≡₂ with wbr-insert b₁ b ∀₂ (f₁ , xs , ys , zs , ≡₂ , f₁∈writes , f₁∈reads)
  where ∀₂ : ∀ f₁ → Script.exec (St.run oracle x₁ sys) b₁ f₁ ≡ St.run oracle _ (Script.exec (St.run oracle x₁ sys) b₁) f₁
        ∀₂ f₁ = subst (λ x₃ → Script.exec (St.run oracle x₃ sys) b₁ f₁ ≡ St.run oracle _ (Script.exec (St.run oracle x₃ sys) b₁) f₁) x≡x₁ (∀₁ f₁)
... | (f₂ , as , bs , cs , ≡₃ , f₂∈writes , f₂∈reads)
  = f₂ , x₁ ∷ as , bs , cs , cong₂ _∷_ x≡x₁ ≡₃ , f₂∈writes , f₂∈reads


lemma4 : {sys : System} {rf b₁ b : Build} (x : Cmd) -> (∀ f₁ → Script.exec sys b₁ f₁ ≡ St.run oracle x (Script.exec sys b₁) f₁) -> ¬ SpeculativeWRHazard sys rf (b₁ ++ x ∷ b) -> ¬ SpeculativeWRHazard sys rf (b₁ ++ b)
lemma4 {sys} {rf} {b₁} {b} x ∀₁ ¬swrh (x₁ , x₂ , wbr , before) = ¬swrh swrh₂
  where swrh₂ : SpeculativeWRHazard sys rf (b₁ ++ x ∷ b)
        swrh₂ = x₁ , x₂ , wbr-insert b₁ b ∀₁ wbr , before

lemma3 : {sys sys₁ : System} {b : Build} -> (∀ f₁ → sys₁ f₁ ≡ sys f₁) -> DisjointBuild sys b -> DisjointBuild sys₁ b 
lemma3 ∀₁ DisjointBuild.Null = DisjointBuild.Null
lemma3 {sys} {sys₁} ∀₁ (DisjointBuild.Cons x x₁ b dsb) = DisjointBuild.Cons x dsj b (lemma3 (λ f₁ → St.lemma2 {oracle} x f₁ ≡₁ (∀₁ f₁)) dsb)
  where ≡₁ : proj₁ (oracle x) sys₁ ≡ proj₁ (oracle x) sys
        ≡₁ = proj₂ (oracle x) sys₁ sys λ f₁ _ → ∀₁ f₁
        dsj : Disjoint (cmdReads x sys₁) (cmdWrites x sys₁)
        dsj = λ x₂ → x₁ (∈-resp-≡ _ (cmdReads x sys₁) (cmdReads x sys) (cong (map proj₁ ∘ proj₁) ≡₁) (proj₁ x₂)
                        , ∈-resp-≡ _ (cmdWrites x sys₁) (cmdWrites x sys) (cong (map proj₁ ∘ proj₂) ≡₁) (proj₂ x₂))

lemma5 : {sys₀ sys : System} (x : Cmd) (ls : Build) -> sys ≡ Script.exec sys₀ (reverse ls) -> St.run oracle x sys ≡ Script.exec sys₀ (reverse (x ∷ ls))
lemma5 {sys₀} x ls ≡₁ = trans (cong (\s -> St.run oracle x s) ≡₁) (trans (g₃ (reverse ls)) (cong (\ xs -> Script.exec sys₀ xs) (sym (unfold-reverse x ls))))
  where g₃ : {sys₁ : System} (xs : Build) -> St.run oracle x (Script.exec sys₁ xs) ≡ Script.exec sys₁ (xs ++ x ∷ [])
        g₃ [] = refl
        g₃ (x₁ ∷ xs) = g₃ xs

{-
-- if there is no hazard then run with error produces right; use hazardfree evidence
completeness : {sys₀ : System} {rf : Build} (b : Build) -> DisjointBuild sys₀ b -> HazardFree sys₀ b [] -> ¬ SpeculativeWRHazard sys₀ rf b -> ∃[ st ](∃[ fi₁ ](execWError ((sys₀ ,  []) , FileInfo.[]) b rf ≡ inj₂ (st , fi₁)))
completeness {sys₀} b dsb hf ¬swrh = g₃ b dsb [] hf ¬swrh refl
  where g₃ : {sys : System} {mm : Memory} {b₁ rf : Build} {fi : FileInfo sys₀ b₁} (b : Build) -> DisjointBuild sys b -> MemoryProperty mm -> HazardFree sys b (readsWrites fi) -> ¬ SpeculativeWRHazard sys₀ rf ((ran fi) ++ b) -> sys ≡ Script.exec sys₀ (ran fi) -> ∃[ st ](∃[ fi₁ ](execWError ((sys ,  mm) , fi) b rf ≡ inj₂ (st , fi₁)))
        g₃ {sys} {mm} {fi} [] dsj mp hf ¬swrh _ = {!!} -- (sys , mm) , (fi , refl)
        g₃ {sys} {mm} {b₁} {rf} {fi} (x ∷ b) (DisjointBuild.Cons .x ds .b dsb) mp (Cons _ .x .b x₁ hf) ¬swrh sys≡ with x ∈? map proj₁ mm
        ... | no x∉ with hasHazard (sys , mm) fi x rf
        ... | nothing = g₃ b dsb (MemoryProperty.Cons x sys (λ f₁ x₂ → St.lemma3 f₁ (proj₂ (proj₁ (oracle x) sys)) λ x₃ → ds (x₂ , x₃)) mp) {!!}
                           (subst (λ x₂ → ¬ SpeculativeWRHazard sys₀ rf x₂) {!!} ¬swrh) (lemma5 x {!!} sys≡)
                           -- (l11 x (ran fi) b)
        ... | just (ReadWrite f₁ ∈₁ ∈₂) = contradiction (∈₁ , g₁ f₁ fi ∈₂) x₁
        ... | just (WriteWrite f₁ ∈₁ ∈₂) = contradiction (∈₁ , g₂ f₁ fi ∈₂) x₁
        ... | just (SpeculativeWriteRead _ x3 wbr bf) = contradiction swrh ¬swrh
          where swrh : SpeculativeWRHazard sys₀ rf ((reverse (map proj₁ fi)) ++ (x ∷ b))
                swrh = x , x3 , {!!} , bf
        g₃ {sys} {mm} {fi} {rf} (x ∷ b) (DisjointBuild.Cons .x ds .b dsb) mp (Cons _ .x .b x₁ hf) ¬swrh sys≡ | yes x∈ with maybeAll {sys} (get x mm x∈)
        ... | nothing with hasHazard (sys , mm) fi x rf
        ... | nothing = g₃ b dsb (MemoryProperty.Cons x sys (λ f₁ x₂ → St.lemma3 f₁ (proj₂ (proj₁ (oracle x) sys)) λ x₃ → ds (x₂ , x₃)) mp) hf (subst (λ x₂ → ¬ SpeculativeWRHazard sys₀ rf x₂) (l11 x (map proj₁ fi) b) ¬swrh) (lemma5 x (map proj₁ fi) sys≡)
        ... | just (ReadWrite f₁ ∈₁ ∈₂) = contradiction (∈₁ , g₁ f₁ fi ∈₂) x₁
        ... | just (WriteWrite f₁ ∈₁ ∈₂) = contradiction (∈₁ , g₂ f₁ fi ∈₂) x₁
        ... | just (SpeculativeWriteRead _ x3 wbr bf) = contradiction {!!} ¬swrh
        g₃ {sys} {mm} {fi} {rf} (x ∷ b) (DisjointBuild.Cons .x ds .b dsb) mp (Cons _ .x .b x₁ hf) ¬swrh sys≡ | yes x∈ | just all₁ with getProperty x mp x∈
        ... | sys₀ , get≡ , ∀₁ = g₃ b (lemma3 ∀≡ dsb) mp (hf-∷⁻-∀ {St.run oracle x sys} {sys} {[]} {[]} refl ∀≡ hf) (lemma4 x (λ f₁ → subst (λ x₂ → x₂ f₁ ≡ St.run oracle x x₂ f₁) sys≡ (∀≡ f₁)) ¬swrh) sys≡
          where all₂ : (ls : List (FileName × Maybe FileContent)) (ls₁ : List FileName) -> All (λ (f₁ , v₁) → sys f₁ ≡ v₁) ls -> ls ≡ map (λ f₁ → f₁ , St.run oracle x sys₀ f₁) ls₁ -> All (λ f₁ → sys f₁ ≡ St.run oracle x sys₀ f₁) ls₁
                all₂ ls [] all₀ ≡₀ = All.[]
                all₂ (x₁ ∷ ls) (x ∷ ls₁) (px All.∷ all₀) ≡₀ with ∷-injective ≡₀
                ... | x₁≡x , ls≡_ = trans (cong (sys ∘ proj₁) (sym x₁≡x)) (trans px (cong proj₂ x₁≡x)) All.∷ (all₂ ls ls₁ all₀ ls≡_)
                ∀≡ : ∀ f₁ → sys f₁ ≡ St.run oracle x sys f₁
                ∀≡ f₁ with f₁ ∈? cmdWrites x sys
                ... | no f₁∉ = St.lemma3 f₁ (proj₂ (proj₁ (oracle x) sys)) f₁∉
                ... | yes f₁∈ = trans (lookup (all₂ (get x mm x∈) (cmdReadWrites x sys₀) all₁ get≡) f₁∈₁) (sym ≡₂)
                  where ≡₃ : proj₁ (oracle x) sys ≡ proj₁ (oracle x) sys₀
                        ≡₃ = sym (proj₂ (oracle x) sys₀ sys λ f₂ x₂ → trans (∀₁ f₂ x₂) (sym (lookup (all₂ (get x mm x∈) (cmdReadWrites x sys₀) all₁ get≡) (∈-++⁺ˡ x₂))))
                        f₁∈₁ : f₁ ∈ cmdReadWrites x sys₀
                        f₁∈₁ = ∈-++⁺ʳ (cmdReads x sys₀) (∈-resp-≡ f₁ (cmdWrites x sys) (cmdWrites x sys₀) (cong (map proj₁ ∘ proj₂) ≡₃) f₁∈)
                        ≡₂ : St.run oracle x sys f₁ ≡ St.run oracle x sys₀ f₁
                        ≡₂ = subst (λ x₂ → foldr extend sys (proj₂ (proj₁ (oracle x) sys)) f₁ ≡ foldr extend sys₀ (proj₂ x₂) f₁)
                                   ≡₃
                                   (St.lemma4 {sys} {sys₀} (proj₂ (proj₁ (oracle x) sys)) f₁ f₁∈)
-}

correct : ∀ sys b ls → HazardFree sys b ls → exec (sys , []) b ≡ exec (exec (sys , []) b) b
correct = {!!}

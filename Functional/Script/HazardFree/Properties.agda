
open import Functional.State as St using (F ; System ; Cmd ; run ; trace ; lemma5 ; lemma1 ; lemma1-sym)  

module Functional.Script.HazardFree.Properties (oracle : F) where

open import Agda.Builtin.Equality
open import Common.List.Properties using (_before_en_ ; ∈→before-∷ʳ ; l9 ; l8 ; l4 ; ∈-resp-≡ ; before-∷ʳ⁺ ; ∃-last)
open import Functional.Build using (Build)
open import Functional.Script.HazardFree.Base (oracle) using (HazardFree ; Null ; Cons ; CmdReadWrites ; CmdWrites ; CmdReads ; HazardFreeReordering ; HFR ; SpeculativeWRHazard ; WriteBeforeRead)
open import Functional.Script.Exec (oracle) using (exec ;  build-rws ; writes ; reads ; h₃ ; h₄ ; h₁ ; read-writes)
open import Functional.Script.Properties (oracle) using (exec≡₅)
open import Data.Empty using (⊥)
open import Data.List using (List ; _∷ʳ_ ; _∷_ ; _++_ ; [] ; map ; reverse ; [_])
open import Data.List.Properties using (++-assoc ; ∷-injective ; ++-identityʳ ; unfold-reverse ; reverse-involutive)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (decSetoid ; subst ; sym ; cong ; cong₂ ; trans)
open import Data.String.Properties using (_≟_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; ∃-syntax ; _×_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-insert)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_ ; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Data.List.Relation.Unary.All.Properties using (¬All⇒Any¬ ; ++⁻ˡ ; ++⁻ʳ)
open import Data.List.Relation.Unary.Any using (there ; here)
open import Function using (_∘_)


{- if we remove the last command from a build, the build is still hazardfree -}
hf-∷ʳ⁻ : {ls : List String} (s : System) (x : Cmd) (xs : Build) -> HazardFree s (xs ∷ʳ x) ls -> HazardFree s xs ls
hf-∷ʳ⁻ s x [] hf = Null
hf-∷ʳ⁻ s x (x₁ ∷ xs) (Cons ls .x₁ .(xs ++ x ∷ []) x₂ hf)
  = Cons ls x₁ xs x₂ (hf-∷ʳ⁻ (run oracle x₁ s) x xs hf)

{- the prefix of a hazardfree build is still hazardfree -}
hf-++⁻ˡ : {b₁ : Build} (s : System) (ls : List String) (b : Build) -> HazardFree s (b ++ b₁) ls -> HazardFree s b ls
hf-++⁻ˡ s ls [] hf = Null
hf-++⁻ˡ s ls (x₁ ∷ b) (Cons .ls .x₁ .(b ++ _) x hf)
  = Cons ls x₁ b x (hf-++⁻ˡ (run oracle x₁ s) (CmdReadWrites s x₁ ++ ls) b hf)

{- get hazardfree suffix of hazardfree build -}
hf-++⁻ʳ : (s : System) (ls : List String) (b b₁ : Build) -> HazardFree s (b ++ b₁) ls -> HazardFree (exec s b) b₁ (build-rws s b ls)
hf-++⁻ʳ s ls [] b₁ hf = hf
hf-++⁻ʳ s ls (x ∷ b) b₁ (Cons .ls .x .(b ++ b₁) x₁ hf)
  = hf-++⁻ʳ (run oracle x s) (CmdReadWrites s x ++ ls) b b₁ hf

{- appending a command to the end of a build is still hazardfree if we know the cmd doesnt write to anything in ls -}
hf-∷ʳ⁺ : (s : System) (ls : List String) (x : Cmd) (b : Build) -> Disjoint (CmdWrites (exec s b) x) (build-rws s b ls) -> HazardFree s b ls -> HazardFree s (b ∷ʳ x) ls
hf-∷ʳ⁺ s ls x [] ds hf = Cons ls x [] ds HazardFree.Null
hf-∷ʳ⁺ s ls x (x₁ ∷ b) ds (Cons .ls .x₁ .b x₂ hf)
  = Cons ls x₁ (b ∷ʳ x) x₂ (hf-∷ʳ⁺ (run oracle x₁ s) (CmdReadWrites s x₁ ++ ls) x b ds hf)

{- appending a build to the end of a hazardfree build is still hazardfree if the 2nd build is hazardfree given the list of files read/written by the first build and the ending system -}
hf-++⁺ : (s : System) (ls : List String) (b b₁ : Build) -> HazardFree s b ls -> HazardFree (exec s b) b₁ (build-rws s b ls) -> HazardFree s (b ++ b₁) ls
hf-++⁺ s ls [] b₁ hf₁ hf₂ = hf₂
hf-++⁺ s ls (x ∷ b) b₁ (Cons .ls .x .b x₁ hf₁) hf₂
  = Cons ls x (b ++ b₁) x₁ (hf-++⁺ (run oracle x s) (CmdReadWrites s x ++ ls) b b₁ hf₁ hf₂)


hf-∷⁻ : {s s₁ : System} {as bs cs ls : List String} -> bs ≡ as -> (b : Build) -> HazardFree s b (as ++ cs ++ ls) -> All (λ f₁ → s₁ f₁ ≡ s f₁) (reads s b) -> HazardFree s₁ b (bs ++ ls)
hf-∷⁻ bs≡as [] hf all₁ = HazardFree.Null
hf-∷⁻ {s} {s₁} {as} {bs} {cs} {ls} bs≡as (x ∷ b) (Cons _ .x .b dsj hf) all₁
  = Cons (bs ++ ls) x b  (λ x₂ → dsj (∈-resp-≡ _ (CmdWrites s₁ x) (CmdWrites s x) (cong (map proj₁ ∘ proj₂) ≡₁) (proj₁ x₂) , v∈ (proj₂ x₂))) hf₁
    where ≡₁ : proj₁ (oracle x) s₁ ≡ proj₁ (oracle x) s
          ≡₁ = sym (proj₂ (oracle x) s s₁ (λ f₁ x₁ → sym (lookup (++⁻ˡ (CmdReads s x) all₁) x₁)))
          ≡₂ : CmdReadWrites s₁ x ≡ CmdReadWrites s x
          ≡₂ = subst (λ x₁ → CmdReadWrites s₁ x ≡ (map proj₁ (proj₁ x₁)) ++ (map proj₁ (proj₂ x₁))) ≡₁ refl
          v∈ : {v : String} -> v ∈ bs ++ ls -> v ∈ as ++ cs ++ ls
          v∈ v∈bs++ls with ∈-++⁻ bs v∈bs++ls
          ... | inj₁ v∈bs = ∈-++⁺ˡ (subst (λ x₁ → _ ∈ x₁) bs≡as v∈bs)
          ... | inj₂ v∈ls = ∈-++⁺ʳ as (∈-++⁺ʳ cs v∈ls)
          hf₁-sub : HazardFree (run oracle x s) b ((CmdReadWrites s x ++ as) ++ cs ++ ls)
          hf₁-sub = subst (λ x₁ → HazardFree (run oracle x s) b x₁) (sym (++-assoc (CmdReadWrites s x) as (cs ++ ls))) hf
          hf₁ : HazardFree (run oracle x s₁) b (CmdReadWrites s₁ x ++ bs ++ ls)
          hf₁ with hf-∷⁻ {run oracle x s} {run oracle x s₁} {CmdReadWrites s x ++ as} {CmdReadWrites s₁ x ++ bs} {cs} {ls} (cong₂ _++_ ≡₂ bs≡as) b hf₁-sub (lemma1-sym {oracle} {s₁} {s} (reads (run oracle x s) b) x (++⁻ˡ (CmdReads s x) all₁) (++⁻ʳ (CmdReads s x) all₁))
          ... | hf₂ = subst (λ x₁ → HazardFree (run oracle x s₁) b x₁) (++-assoc (CmdReadWrites s₁ x) bs ls) hf₂

hf-∷⁻-∀ : {s s₁ : System} {as bs cs ls : List String} {b : Build} -> bs ≡ as -> (∀ f₁ → s₁ f₁ ≡ s f₁) -> HazardFree s b (as ++ cs ++ ls) -> HazardFree s₁ b (bs ++ ls)
hf-∷⁻-∀ bs≡as ∀₁ HazardFree.Null = HazardFree.Null
hf-∷⁻-∀ {s} {s₁} {as} {bs} {cs} {ls} bs≡as ∀₁ (Cons _ x b dsj hf) = Cons (bs ++ ls) x b dsj₁ hf₁
  where ≡₁ : proj₁ (oracle x) s₁ ≡ proj₁ (oracle x) s
        ≡₁ = proj₂ (oracle x) s₁ s λ f₁ x₁ → ∀₁ f₁
        ≡₂ : CmdReadWrites s₁ x ≡ CmdReadWrites s x
        ≡₂ = cong₂ _++_ (cong (map proj₁ ∘ proj₁) ≡₁) (cong (map proj₁ ∘ proj₂) ≡₁)
        ∈₁ : {v : String} -> v ∈ (bs ++ ls) -> v ∈ (as ++ cs ++ ls)
        ∈₁ v∈bs++ls with ∈-++⁻ bs v∈bs++ls
        ... | inj₁ v∈bs = ∈-++⁺ˡ (∈-resp-≡ _ bs as bs≡as v∈bs)
        ... | inj₂ v∈ls = ∈-++⁺ʳ as (∈-++⁺ʳ cs v∈ls)
        dsj₁ : Disjoint (CmdWrites s₁ x) (bs ++ ls)
        dsj₁ = λ x₁ → dsj (∈-resp-≡ _ (CmdWrites s₁ x) (CmdWrites s x) (cong (map proj₁ ∘ proj₂) ≡₁) (proj₁ x₁)
                           , ∈₁ (proj₂ x₁))
        hf-sub : HazardFree (run oracle x s) b ((CmdReadWrites s x ++ as) ++ cs ++ ls)
        hf-sub = subst (λ x₁ → HazardFree (run oracle x s) b x₁) (sym (++-assoc (CmdReadWrites s x) as (cs ++ ls))) hf
        hf₁ : HazardFree (run oracle x s₁) b (CmdReadWrites s₁ x ++ bs ++ ls)
        hf₁ = subst (λ x₁ → HazardFree (run oracle x s₁) b x₁) (++-assoc (CmdReadWrites s₁ x) bs ls) (hf-∷⁻-∀ (cong₂ _++_ ≡₂ bs≡as) (λ f₁ → St.lemma2 {oracle} x f₁ ≡₁ (∀₁ f₁)) hf-sub)


{- if we remove x from the middle of the build, it is still hazardfree if we know that x doesn't write to anything read by b₁ -}
hf-drop-mid : {s : System} {ls : List String} (x : Cmd) (b b₁ : Build) -> Disjoint (CmdWrites (exec s b) x) (reads (run oracle x (exec s b)) b₁) -> HazardFree s (b ++ x ∷ b₁) ls -> HazardFree s (b ++ b₁) ls
hf-drop-mid {sys} {ls} x b [] ds hf = subst (λ x₁ → HazardFree sys x₁ _) (sym (++-identityʳ b)) (hf-∷ʳ⁻ sys x b hf)
hf-drop-mid {sys} {ls} x b (x₁ ∷ b₁) ds hf with ∃-last x₁ b₁ -- last x₁ b₁
... | x₂ , b₂ , b₂∷ᴿx₂≡x₁∷b₁ = hf-++⁺ sys ls b (x₁ ∷ b₁) hf₁ hf₂
  where hf₁ : HazardFree sys b ls
        hf₁ = hf-++⁻ˡ sys ls b hf
        hf₂ : HazardFree (exec sys b) (x₁ ∷ b₁) (build-rws sys b ls)
        hf₂ with hf-++⁻ʳ sys ls b (x ∷ x₁ ∷ b₁) hf
        ... | Cons _ _ _ _ hf₃
          = hf-∷⁻ {run oracle x (exec sys b)} {exec sys b} {[]} {[]} {read-writes (exec sys b) x} {build-rws sys b ls} refl (x₁ ∷ b₁) hf₃ (lemma5 (reads (run oracle x (exec sys b)) (x₁ ∷ b₁)) (proj₂ (proj₁ (oracle x) (exec sys b))) ds)


hf→disjoint : {ls : List String} (ls₁ : List String) (s : System) (xs : Build) -> HazardFree s xs (ls₁ ++ ls) -> Disjoint ls₁ (writes s xs)
hf→disjoint ls₁ s [] hf = λ ()
hf→disjoint {ls} ls₁ s (x ∷ xs) (Cons _ .x .xs dsj hf)
  = λ x₁ → g₁ (proj₁ x₁) (proj₂ x₁)
    where hf₂ : HazardFree (run oracle x s) xs ((CmdReadWrites s x ++ ls₁) ++ ls)
          hf₂ = subst (λ x₁ → HazardFree _ _ x₁) (sym (++-assoc (CmdReadWrites s x) ls₁ ls)) hf
          g₁ : {v : String} -> v ∈ ls₁ -> v ∈ CmdWrites s x ++ writes (run oracle x s) xs -> ⊥
          g₁ v∈ls₁ v∈CmdWrites++writes with ∈-++⁻ (CmdWrites s x) v∈CmdWrites++writes
          ... | inj₁ v∈CmdWrites = dsj (v∈CmdWrites , ∈-++⁺ˡ v∈ls₁)
          ... | inj₂ v∈writes = (hf→disjoint (CmdReadWrites s x ++ ls₁) (run oracle x s) xs hf₂)
                                (∈-++⁺ʳ (CmdReadWrites s x) v∈ls₁ , v∈writes)

hf→disjointWrites : {ls : List String} (s : System) (x : Cmd) (xs : Build) -> HazardFree s (x ∷ xs) ls -> Disjoint (CmdWrites s x) (writes (run oracle x s) xs)
hf→disjointWrites s x xs (Cons _ .x .xs dsj hf) = λ x₁ → g₁ (proj₁ x₁) (proj₂ x₁)
  where g₁ : {v : String} -> v ∈ CmdWrites s x -> v ∈ writes (run oracle x s) xs -> ⊥
        g₁ v∈CmdWrites v∈writes = (hf→disjoint (CmdReadWrites s x) (run oracle x s) xs hf)
                                  (∈-++⁺ʳ (CmdReads s x) v∈CmdWrites , v∈writes)

hf→disjointReads : {ls : List String} (s : System) (x : Cmd) (xs : Build) -> HazardFree s (x ∷ xs) ls -> Disjoint (CmdReads s x) (writes (run oracle x s) xs)
hf→disjointReads s x xs (Cons _ .x .xs x₁ hf) = λ x₂ → g₁ (proj₁ x₂) (proj₂ x₂)
  where g₁ : {v : String} -> v ∈ CmdReads s x -> v ∈ writes (run oracle x s) xs -> ⊥
        g₁ v∈CmdReads v∈writes = (hf→disjoint (CmdReadWrites s x) (run oracle x s) xs hf)
                                 (∈-++⁺ˡ v∈CmdReads , v∈writes)

∃read : (s : System) (v : String) (xs : Build) -> v ∈ reads s xs -> ∃[ x₁ ](∃[ ys ](∃[ zs ](xs ≡ ys ++ x₁ ∷ zs × v ∈ CmdReads (exec s ys) x₁)))
∃read s v (x ∷ xs) v∈ with ∈-++⁻ (CmdReads s x) v∈
... | inj₁ v∈Creads = x , [] , xs , refl , v∈Creads
... | inj₂ v∈reads with ∃read (run oracle x s) v xs v∈reads
... | x₁ , ys₁ , zs₁ , xs≡ys₁++x₁∷zs₁ , v∈Creads
  = x₁ , (x ∷ ys₁) , zs₁ , (cong (x ∷_) xs≡ys₁++x₁∷zs₁) , v∈Creads

wbr-insert : {s : System} (v w x : Cmd) (xs ys : Build) -> Disjoint (CmdWrites (exec s xs) x) (reads (run oracle x (exec s xs)) ys) -> WriteBeforeRead s v w (xs ++ ys) -> WriteBeforeRead s v w (xs ++ x ∷ ys)
wbr-insert {s} v w x [] ys dsj (f₁ , ls₁ , ls₂ , ls₃ , ys≡ls₁++v∷ls₂++w∷ls₃ , f₁∈writes-v , f₁∈reads-w)
  = f₁ , x ∷ ls₁ , ls₂ , ls₃ , cong (x ∷_) ys≡ls₁++v∷ls₂++w∷ls₃ , f₁∈writes-v₂ , f₁∈reads-w₂
  where dsj₂ : Disjoint (CmdWrites s x) (reads (run oracle x s) (ls₁ ++ v ∷ ls₂ ++ w ∷ ls₃))
        dsj₂ = λ x₁ → dsj (proj₁ x₁ , subst (λ x₂ → _ ∈ reads (run oracle x s) x₂) (sym ys≡ls₁++v∷ls₂++w∷ls₃) (proj₂ x₁))
        all₂ : All (λ f₂ → s f₂ ≡ run oracle x s f₂) (reads (run oracle x s) (ls₁ ++ v ∷ ls₂ ++ w ∷ ls₃))
        all₂ = lemma5 {s} (reads (run oracle x s) (ls₁ ++ v ∷ ls₂ ++ w ∷ ls₃)) (proj₂ (proj₁ (oracle x) s)) dsj₂
        f₁∈writes-v₂ : f₁ ∈ CmdWrites (exec (run oracle x s) ls₁) v
        f₁∈writes-v₂ with h₃ {s} {run oracle x s} v ls₁ (ls₂ ++ w ∷ ls₃) all₂
        ... | all₃ = subst (λ x₁ → f₁ ∈ map proj₁ (proj₂ x₁)) (h₄ (exec s ls₁) (exec (run oracle x s) ls₁) v all₃) f₁∈writes-v
        f₁∈reads-w₂ : f₁ ∈ CmdReads (exec s ((x ∷ ls₁) ++ v ∷ ls₂)) w
        f₁∈reads-w₂ with h₃ {s} {run oracle x s} w (ls₁ ++ v ∷ ls₂) ls₃ (subst (λ x₁ → All (λ f₂ → s f₂ ≡ run oracle x s f₂) (reads (run oracle x s) x₁)) (l8 ls₁) all₂)
        ... | all₃ = subst (λ x₁ → f₁ ∈ map proj₁ (proj₁ x₁)) (h₄ (exec s (ls₁ ++ v ∷ ls₂)) (exec (run oracle x s) (ls₁ ++ v ∷ ls₂)) w all₃) f₁∈reads-w
                
wbr-insert {s} v w x (x₁ ∷ xs) ys dsj (f₁ , [] , ls₂ , ls₃ , x₁∷xs++ys≡v∷ls₂++w∷ls₃ , f₁∈writes-v , f₁∈reads-w) with ∷-injective x₁∷xs++ys≡v∷ls₂++w∷ls₃
... | x₁≡v , xs++ys≡ls₂++w∷ls₃ with h₁ {run oracle v s} f₁ x w xs ys ls₂ ls₃ f₁∈reads-w dsj₂ xs++ys≡ls₂++w∷ls₃
  where dsj₂ : Disjoint (CmdWrites (exec (run oracle v s) xs) x) (reads (run oracle x (exec (run oracle v s) xs)) ys)
        dsj₂ = λ x₂ → dsj (subst (λ x₃ → _ ∈ CmdWrites (exec (run oracle x₃ s) xs) x) (sym x₁≡v) (proj₁ x₂)
                          , subst (λ x₃ → _ ∈ reads (run oracle x (exec (run oracle x₃ s) xs)) ys) (sym x₁≡v) (proj₂ x₂))
... | ls₄ , ls₅ , xs++x∷ys≡ls₄++w∷ls₅ , f₁∈reads-w₂
  = f₁ , [] , ls₄ , ls₅ , cong₂ _∷_ x₁≡v xs++x∷ys≡ls₄++w∷ls₅ , f₁∈writes-v , f₁∈reads-w₂

wbr-insert {sys} v w x (x₁ ∷ xs) ys dsj (f₁ , x₂ ∷ ls₁ , ls₂ , ls₃ , x₁∷xs++ys≡x₂∷ls₁++v∷ls₂++w∷ls₃ , f₁∈writes-v , f₁∈reads-w) with ∷-injective x₁∷xs++ys≡x₂∷ls₁++v∷ls₂++w∷ls₃
... | x₁≡x₂ , xs++ys≡ls₁++v∷ls₂++w∷ls₃ with wbr-insert {run oracle x₂ sys} v w x xs ys  dsj₂ (f₁ , ls₁ , ls₂ , ls₃ , xs++ys≡ls₁++v∷ls₂++w∷ls₃ , f₁∈writes-v , f₁∈reads-w)
  where dsj₂ : Disjoint (CmdWrites (exec (run oracle x₂ sys) xs) x) (reads (run oracle x (exec (run oracle x₂ sys) xs)) ys)
        dsj₂ = λ x₃ → dsj (subst (λ x₄ → _ ∈ CmdWrites (exec (run oracle x₄ sys) xs) x) (sym x₁≡x₂) (proj₁ x₃)
                          , subst (λ x₄ → _ ∈ reads (run oracle x (exec (run oracle x₄ sys) xs)) ys) (sym x₁≡x₂) (proj₂ x₃))
... | f₂ , ls₄ , ls₅ , ls₆ , xs∷ʳx++ys≡ls₄++v∷ls₅++w∷ls₆ , f₂∈writes-v , f₂∈reads-w
  = f₂ , x₂ ∷ ls₄ , ls₅ , ls₆ , cong₂ _∷_ x₁≡x₂ xs∷ʳx++ys≡ls₄++v∷ls₅++w∷ls₆ , f₂∈writes-v , f₂∈reads-w



{- if we have a pair of reordered builds, and ∃ v s.t v ∈ writes of x in 2nd build and v ∈ reads of zs in the 2nd build, then ∃ a speculative wr hazard -}
∃swrh : {v : String} (s : System) (x : Cmd) (xs ys zs : Build) -> xs ∷ʳ x ↭ ys ++ x ∷ zs -> v ∈ CmdWrites (exec s ys) x -> v ∈ reads (run oracle x (exec s ys)) zs -> SpeculativeWRHazard s (xs ∷ʳ x) (ys ++ x ∷ zs)
∃swrh {v} s x xs ys zs ↭₁ v∈Cwrites v∈reads with ∃read (run oracle x (exec s ys)) v zs v∈reads
... | x₁ , as , bs , zs≡as++x₁∷bs , v∈Creads
  = x₁ , x , wbr , before
    where wbr : WriteBeforeRead s x x₁ (ys ++ x ∷ zs)
          wbr = v , ys , as , bs , cong (ys ++_) (cong (x ∷_) zs≡as++x₁∷bs) , v∈Cwrites
              , subst (λ x₂ → v ∈ proj₁ (trace oracle x₂ x₁)) (exec≡₅ {s} x ys as) v∈Creads
          before : x₁ before x en (xs ∷ʳ x)
          before = ∈→before-∷ʳ x₁ x xs (∈-resp-↭ (↭-sym (l9 x xs ys zs ↭₁))
                                             (∈-++⁺ʳ ys (subst (λ x₅ → x₁ ∈ x₅)
                                                              (sym zs≡as++x₁∷bs)
                                                              (∈-insert as))))


swrh-∷ʳ⁻ : (s : System) (x : Cmd) (b b₁ b₂ : Build) -> ¬ SpeculativeWRHazard s (b ∷ʳ x) (b₁ ++ x ∷ b₂) -> Disjoint (CmdWrites (exec s b₁) x) (reads (run oracle x (exec s b₁)) b₂) -> ¬ SpeculativeWRHazard s b (b₁ ++ b₂)
swrh-∷ʳ⁻ s x b b₁ b₂ ¬sp-wr-hz dsj = λ x₁ → ¬sp-wr-hz (g₁ x₁)
  where g₁ : SpeculativeWRHazard s b (b₁ ++ b₂) -> SpeculativeWRHazard s (b ∷ʳ x) (b₁ ++ x ∷ b₂)
        g₁ (x₀ , x₂ , wbr , before) = x₀ , x₂ , (wbr-insert x₂ x₀ x b₁ b₂ dsj wbr) , (before-∷ʳ⁺ x₀ x₂ x b before)


-- in a hazard free reordering where we consider the last command in the original order.
-- we know that command cannot write to any file read by a command that occurs after in in the reorder
hfr→disjoint : (s : System) (x : Cmd) (xs ys zs : Build) -> HazardFreeReordering s (xs ∷ʳ x) (ys ++ x ∷ zs) -> Disjoint (CmdWrites (exec s ys) x) (reads (run oracle x (exec s ys)) zs)
hfr→disjoint s x xs ys zs (HFR _ _ ↭₁ hf₁ hf₂ ¬swrh) = λ x₁ → ¬swrh (∃swrh s x xs ys zs ↭₁ (proj₁ x₁) (proj₂ x₁))


hfr-∷ʳ⁻ : {sys : System} (x : Cmd) (b b₁ b₂ : Build) -> HazardFreeReordering sys (b ∷ʳ x) (b₁ ++ x ∷ b₂) -> HazardFreeReordering sys b (b₁ ++ b₂)
hfr-∷ʳ⁻ {sys} x b b₁ b₂ hfr@(HFR b₃ b₄  b₃↭b₄ hf hf₁ ¬sp-wr-haz) = HFR b (b₁ ++ b₂) (l9 x b b₁ b₂ b₃↭b₄) (hf-∷ʳ⁻ sys x b hf) (hf-drop-mid x b₁ b₂ (hfr→disjoint sys x b b₁ b₂ hfr) hf₁) (swrh-∷ʳ⁻ sys x b b₁ b₂ ¬sp-wr-haz (hfr→disjoint sys x b b₁ b₂ hfr))


{- can produce bottom if we know a write occurs twice in a hazard free build 
hf-⊥ : (f₁ : FileName) -> f₁ ∈ ls -> f₁ ∈ writes sys b -> HazardFree sys b ls -> ⊥
hf-⊥ f₁ f₁∈ls f₁∈writes hf = {!!}
-}









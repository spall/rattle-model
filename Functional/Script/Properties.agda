
open import Functional.State as St using (F ; System ; Cmd ; run ; trace)

module Functional.Script.Properties (oracle : F) where

open import Agda.Builtin.Equality
open import Data.Empty using (⊥)
open import Functional.Build using (Build)
open import Functional.Script.Exec (oracle) as S
open import Data.List using (List ; _∷ʳ_ ; _∷_ ; _++_ ; [] ; reverse ; map ; foldr)
open import Data.List.Properties using (++-identityʳ ; ++-assoc) 
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (subst ; sym ; decSetoid ; trans ; cong ; cong₂ ; cong-app)
open import Common.List.Properties as CLP
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.Product using (proj₂ ; proj₁ ; _,_ ; ∃-syntax ; _×_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.String.Properties using (_≟_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈?_ ; _∉_ ; _∈_)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Data.List.Relation.Unary.All.Properties using (++⁻ ; ++⁻ˡ)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ ; ∈-++⁺ˡ ; ∈-++⁻ ; ∈-insert)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Function using (_∘_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_ ; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Nullary using (yes ; no)
--- ---

h₅ : (s s₁ : System) (x : Cmd) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (Creads s₁ x) -> proj₁ (oracle x) s ≡ proj₁ (oracle x) s₁
h₅ s s₁ x all₁ = sym (proj₂ (oracle x) s₁ s λ f₁ x₁ → sym (lookup all₁ x₁))


--- exec properties ---

exec-∷ʳ : (s : System) (x : Cmd) (b : Build) -> run oracle x (S.exec s b) ≡ S.exec s (b ∷ʳ x)
exec-∷ʳ s x [] = refl
exec-∷ʳ s x (x₁ ∷ b) = exec-∷ʳ (run oracle x₁ s) x b

exec-∷≡ : (f₁ : String) (s s₁ : System) (b : Build) -> All (λ f₂ → s f₂ ≡ s₁ f₂) (reads s₁ b) -> s f₁ ≡ s₁ f₁ -> exec s b f₁ ≡ exec s₁ b f₁
exec-∷≡ f₁ s s₁ [] all₁ ≡₁ = ≡₁
exec-∷≡ f₁ s s₁ (x₁ ∷ b) all₁ ≡₁ with ++⁻ (Creads s₁ x₁) all₁ 
... | all₂ , all₃ = exec-∷≡ f₁ (run oracle x₁ s) (run oracle x₁ s₁) b (St.lemma1-sym {oracle} {s} {s₁} (reads (run oracle x₁ s₁) b) x₁ all₂ all₃)
                            (St.lemma2 {oracle} {s} {s₁} x₁ f₁ (h₄ s s₁ x₁ all₂) ≡₁)


-- this is a copy of lemma9 so just replace lemma9 with this
exec-≡sys : (s : System) (f₁ : String) (xs : Build) -> f₁ ∉ writes s xs -> exec s xs f₁ ≡ s f₁
exec-≡sys s f₁ [] f₁∉ = refl
exec-≡sys s f₁ (x ∷ xs) f₁∉ = trans (exec-≡sys (run oracle x s) f₁ xs (λ x₁ → f₁∉ (∈-++⁺ʳ (Cwrites s x) x₁)))
                                    (sym (St.lemma3 {s} f₁ (proj₂ (proj₁ (oracle x) s)) λ x₁ → f₁∉ (∈-++⁺ˡ x₁)))

-- use me in latest proof goal
{- if f₁ is not in the writes if ys then f₁ is the same in the system before and after ys executes -}
exec-≡f₁ : (s : System) (f₁ : String) (xs ys : Build) -> f₁ ∉ writes (exec s xs) ys -> exec s xs f₁ ≡ exec s (xs ++ ys) f₁
exec-≡f₁ s f₁ [] ys f₁∉ = sym (exec-≡sys s f₁ ys f₁∉)
exec-≡f₁ s f₁ (x ∷ xs) ys f₁∉ = exec-≡f₁ (run oracle x s) f₁ xs ys f₁∉

-- i think i can just use foldr-∷ʳ if i redefine the function using foldr
build-rws-∷ʳ : (s : System) (ls : List String) (x : Cmd) (b : Build) -> S.read-writes (S.exec s b) x ++ S.build-rws s b ls ≡ S.build-rws s (b ∷ʳ x) ls
build-rws-∷ʳ s ls x [] = refl
build-rws-∷ʳ s ls x (x₁ ∷ b) = build-rws-∷ʳ (run oracle x₁ s) (S.read-writes s x₁ ++ ls) x b


--- HazardFree properties ---

{- if we remove the last command from a build, the build is still hazardfree -}
∷ʳ⁻ : {ls : List String} (s : System) (x : Cmd) (xs : Build) -> HazardFree s (xs ∷ʳ x) ls -> HazardFree s xs ls
∷ʳ⁻ s x [] hf = HazardFree.Null
∷ʳ⁻ s x (x₁ ∷ xs) (Cons .x₁ .(xs ++ x ∷ []) ls x₂ hf)
  = Cons x₁ xs ls x₂ (∷ʳ⁻ (run oracle x₁ s) x xs hf)


{- the prefix of a hazardfree build is still hazardfree -}
{- seem to need the reverses so we can loop over b₁.... since we remove from end. its a little awkward -}
hf-++⁻ˡ : (s : System) (ls : List String) (x : Cmd) (b b₁ : Build) -> HazardFree s (b ++ (reverse (x ∷ b₁))) ls -> HazardFree s b ls
hf-++⁻ˡ s ls x [] b₁ hf = HazardFree.Null
hf-++⁻ˡ s ls x (x₁ ∷ b) [] hf = ∷ʳ⁻ s x (x₁ ∷ b) hf
hf-++⁻ˡ s ls x (x₁ ∷ b) (x₂ ∷ b₁) hf with ∷ʳ⁻ s x ((x₁ ∷ b) ++ (reverse (x₂ ∷ b₁))) (subst (λ x₃ → HazardFree s x₃ ls) (CLP.l3 x (x₁ ∷ b) (x₂ ∷ b₁)) hf)
... | hf₁ = hf-++⁻ˡ s ls x₂ (x₁ ∷ b) b₁ hf₁


{- appending a command to the end of a build is still hazardfree if we know the cmd doesnt write to anything in ls -}
∷ʳ⁺ : (s : System) (ls : List String) (x : Cmd) (b : Build) -> Disjoint (proj₂ (trace oracle (S.exec s b) x)) (S.build-rws s b ls) -> HazardFree s b ls -> HazardFree s (b ∷ʳ x) ls
∷ʳ⁺ s ls x [] ds hf = Cons x [] ls ds HazardFree.Null
∷ʳ⁺ s ls x (x₁ ∷ b) ds (Cons .x₁ .b .ls x₂ hf)
  = Cons x₁ (b ∷ʳ x) ls x₂ (∷ʳ⁺ (run oracle x₁ s) ((S.read-writes s x₁) ++ ls) x b ds hf)


{- get hazardfree suffix of hazardfree build -}
++⁻ʳ : (s : System) (ls : List String) (b b₁ : Build) -> HazardFree s (b ++ b₁) ls -> HazardFree (S.exec s b) b₁ (S.build-rws s b ls)
++⁻ʳ s ls [] b₁ hf = hf
++⁻ʳ s ls (x ∷ b) b₁ (Cons .x .(b ++ b₁) .ls x₁ hf)
  = ++⁻ʳ (run oracle x s) (S.read-writes s x ++ ls) b b₁ hf

{- appending a build to the end of a hazardfree build is still hazardfree if the 2nd build is hazardfree given the list of files read/written by the first build and the ending system -}
++⁺ : (s : System) (ls : List String) (b b₁ : Build) -> HazardFree s b ls -> HazardFree (S.exec s b) b₁ (S.build-rws s b ls) -> HazardFree s (b ++ b₁) ls
++⁺ s ls b [] hf-b hf-b₁ = subst (λ x → HazardFree s x ls) (sym (++-identityʳ b)) hf-b
++⁺ s ls b (x ∷ b₁) hf-b (Cons .x .b₁ .(S.build-rws s b ls) x₁ hf-b₁) with ∷ʳ⁺ s ls x b x₁ hf-b
... | hf-b∷ʳx with ++⁺ s ls (b ∷ʳ x) b₁ hf-b∷ʳx (subst (λ x₂ → HazardFree (S.exec s (b ∷ʳ x)) b₁ x₂) (build-rws-∷ʳ s ls x b) (subst (λ x₂ → HazardFree x₂ b₁ ((S.read-writes (S.exec s b) x) ++ S.build-rws s b ls)) (exec-∷ʳ s x b) hf-b₁))
... | a = subst (λ x₂ → HazardFree s x₂ ls) (CLP.l4 x b) a

hf→dsj₂ : {ls : List String} (ls₁ : List String) (s : System) (xs : Build) -> HazardFree s xs (ls₁ ++ ls) -> Disjoint ls₁ (writes s xs)
hf→dsj₂ ls₁ s [] hf = λ ()
hf→dsj₂ {ls} ls₁ s (x ∷ xs) (Cons .x .xs .(ls₁ ++ _) dsj hf) with hf→dsj₂ ((read-writes s x) ++ ls₁) (run oracle x s) xs (subst (λ x₁ → HazardFree _ _ x₁) (sym (++-assoc (read-writes s x) ls₁ ls)) hf)
... | dsj₂ = λ x₁ → g₁ (proj₁ x₁) (proj₂ x₁)
  where g₁ : {v : String} -> v ∈ ls₁ -> v ∈ (Cwrites s x) ++ writes (run oracle x s) xs -> ⊥
        g₁ v∈ls₁ v∈Cwrites++writes with ∈-++⁻ (Cwrites s x) v∈Cwrites++writes
        ... | inj₁ v∈Cwrites = dsj (v∈Cwrites , ∈-++⁺ˡ v∈ls₁)
        ... | inj₂ v∈writes = dsj₂ (∈-++⁺ʳ (read-writes s x) v∈ls₁ , v∈writes)

hf→dsj : {ls : List String} (s : System) (x : Cmd) (xs : Build) -> HazardFree s (x ∷ xs) ls -> Disjoint (Cwrites s x) (writes (run oracle x s) xs)
hf→dsj s x xs (Cons .x .xs _ dsj hf) with hf→dsj₂ (read-writes s x) (run oracle x s) xs hf
... | dsj₂ = λ x₁ → g₁ (proj₁ x₁) (proj₂ x₁)
  where g₁ : {v : String} -> v ∈ Cwrites s x -> v ∈ writes (run oracle x s) xs -> ⊥
        g₁ v∈Cwrites v∈writes = dsj₂ (∈-++⁺ʳ (Creads s x) v∈Cwrites , v∈writes)

hf→dsj-reads : {ls : List String} (s : System) (x : Cmd) (xs : Build) -> HazardFree s (x ∷ xs) ls -> Disjoint (Creads s x) (writes (run oracle x s) xs)
hf→dsj-reads s x xs (Cons .x .xs _ x₁ hf) with hf→dsj₂ (read-writes s x) (run oracle x s) xs hf
... | dsj₂ = λ x₂ → g₁ (proj₁ x₂) (proj₂ x₂)
  where g₁ : {v : String} -> v ∈ Creads s x -> v ∈ writes (run oracle x s) xs -> ⊥
        g₁ v∈Creads v∈writes = dsj₂ (∈-++⁺ˡ v∈Creads , v∈writes)
-----------------------------------------

all≡ : (s : System) (fs : List String) (xs ys zs : Build) -> Disjoint fs (writes (exec s ys) zs) -> (∀ f₁ → exec s xs f₁ ≡ exec s (ys ++ zs) f₁) -> All (λ f₁ → exec s xs f₁ ≡ exec s ys f₁) fs
all≡ s [] xs ys zs dsj ∀₁ = All.[]
all≡ s (x ∷ fs) xs ys zs dsj ∀₁ = trans (∀₁ x) (sym (exec-≡f₁ s x ys zs λ x₁ → dsj (here refl , x₁))) All.∷ (all≡ s fs xs ys zs (λ x₁ → dsj (there (proj₁ x₁) , proj₂ x₁)) ∀₁)

writes≡ : (s s₁ : System) (ys : Build) -> All (λ f₁ → s f₁ ≡ s₁ f₁) (reads s₁ ys) -> writes s ys ≡ writes s₁ ys
writes≡ s s₁ [] all₁ = refl
writes≡ s s₁ (x₁ ∷ ys) all₁ with ++⁻ (Creads s₁ x₁) all₁
... | all₂ , all₃ = cong₂ _++_ (cong ((map proj₁) ∘ proj₂) (h₅ s s₁ x₁ all₂))
                                    (writes≡ (run oracle x₁ s) (run oracle x₁ s₁) ys (St.lemma1-sym {oracle} {s} {s₁} (reads (run oracle x₁ s₁) ys) x₁ all₂ all₃))

-- basically a wrapper around subst but nice for writing lemmas because it keeps code less confusing
still-disjoint : (s : System) (x : Cmd) (ys : Build) -> Disjoint (Cwrites s x) (reads (run oracle x s) ys) -> Disjoint (Creads s x) (writes (run oracle x s) ys) -> Disjoint (Creads s x) (writes s ys)
still-disjoint s x ys dsj₁ dsj₂ = subst (λ x₁ → Disjoint _ x₁) (sym (writes≡ s (run oracle x s) ys (St.lemma5 {s} (reads (run oracle x s) ys) (proj₂ (proj₁ (oracle x) s)) dsj₁))) dsj₂


∃read : (s : System) (v : String) (xs : Build) -> v ∈ reads s xs -> ∃[ x₁ ](∃[ ys ](∃[ zs ](xs ≡ ys ++ x₁ ∷ zs × v ∈ Creads (exec s ys) x₁)))
∃read s v (x ∷ xs) v∈ with ∈-++⁻ (Creads s x) v∈
... | inj₁ v∈Creads = x , [] , xs , refl , v∈Creads
... | inj₂ v∈reads with ∃read (run oracle x s) v xs v∈reads
... | x₁ , ys₁ , zs₁ , xs≡ys₁++x₁∷zs₁ , v∈Creads
  = x₁ , (x ∷ ys₁) , zs₁ , (cong (x ∷_) xs≡ys₁++x₁∷zs₁) , v∈Creads


{- if we have a pair of reordered builds, and ∃ v s.t v ∈ writes of x in 2nd build and v ∈ reads of zs in the 2nd build, then ∃ a speculative wr hazard -}
∃swrh : {v : String} (s : System) (x : Cmd) (xs ys zs : Build) -> xs ∷ʳ x ↭ ys ++ x ∷ zs -> v ∈ Cwrites (exec s ys) x -> v ∈ reads (run oracle x (exec s ys)) zs -> speculative-wr-hazard s (xs ∷ʳ x) (ys ++ x ∷ zs)
∃swrh {v} s x xs ys zs ↭₁ v∈Cwrites v∈reads with ∃read (run oracle x (exec s ys)) v zs v∈reads
... | x₁ , as , bs , zs≡as++x₁∷bs , v∈Creads
  = x₁ , x , wbr , before
    where wbr : write-before-read s x x₁ (ys ++ x ∷ zs)
          wbr = v , ys , as , bs , cong (ys ++_) (cong (x ∷_) zs≡as++x₁∷bs) , v∈Cwrites
              , subst (λ x₂ → v ∈ proj₁ (trace oracle x₂ x₁)) (exec≡₂ {s} x ys as) v∈Creads
          before : x₁ before x en (xs ∷ʳ x)
          before = lemma6 x₁ x xs (∈-resp-↭ (↭-sym (CLP.l9 x xs ys zs ↭₁))
                                             (∈-++⁺ʳ ys (subst (λ x₅ → x₁ ∈ x₅)
                                                              (sym zs≡as++x₁∷bs)
                                                              (∈-insert as))))



-- in a hazard free reordering where we consider the last command in the original order.
-- we know that command cannot write to any file read by a command that occurs after in in the reorder
hfr→dsj : (s : System) (x : Cmd) (xs ys zs : Build) -> HazardFreeReordering s (xs ∷ʳ x) (ys ++ x ∷ zs) -> Disjoint (Cwrites (exec s ys) x) (reads (run oracle x (exec s ys)) zs)
hfr→dsj s x xs ys zs (HFR _ _ ↭₁ hf₁ hf₂ ¬swrh) = λ x₁ → ¬swrh (∃swrh s x xs ys zs ↭₁ (proj₁ x₁) (proj₂ x₁))


exec-f₁≡ : (s : System) (f₁ : String) (x : Cmd) (xs ys zs : Build) -> (∀ f₂ → exec s xs f₂ ≡ exec s (ys ++ zs) f₂) -> proj₁ (oracle x) (exec s xs) ≡ proj₁ (oracle x) (exec s ys) -> All (λ f₂ → exec s ys f₂ ≡ run oracle x (exec s ys) f₂) (reads (run oracle x (exec s ys)) zs) -> Disjoint (Cwrites (exec s ys) x) (writes (run oracle x (exec s ys)) zs) -> exec s (xs ∷ʳ x) f₁ ≡ exec s (ys ++ x ∷ zs) f₁
exec-f₁≡ s f₁ x xs ys zs ∀₁ ≡₀ all₁ dsj with f₁ ∈? Cwrites (exec s xs) x
... | yes f₁∈ with exec-≡sys (run oracle x (exec s ys)) f₁ zs f₁∉
  where f₁∉ : f₁ ∉ writes (run oracle x (exec s ys)) zs
        f₁∉ = λ x₁ → dsj (subst (λ x₂ → f₁ ∈ map proj₁ (proj₂ x₂)) ≡₀ f₁∈ , x₁)
... | a = trans ≡₁ (trans (sym a) (cong-app (exec≡₂ {s} x ys zs) f₁))
  where ≡₁ : exec s (xs ∷ʳ x) f₁ ≡ run oracle x (exec s ys) f₁
        ≡₁ with (cong proj₂ ≡₀)
        ... | a₁ with St.lemma4 {exec s xs} {exec s ys} (proj₂ (proj₁ (oracle x) (exec s xs))) f₁ f₁∈
        ... | a₂ = trans (cong-app (sym (exec≡₃ {s} x xs)) f₁) (subst (λ x₁ → foldr St.extend (exec s xs) (proj₂ (proj₁ (oracle x) (exec s xs))) f₁ ≡ foldr St.extend (exec s ys) (proj₂ x₁) f₁) ≡₀ a₂)
-- prove exec s (xs ∷ʳ x) f₁ ≡ run oracle x (exec s ys) f₁ ≡ exec s (ys ++ x ∷ zs) f₁
exec-f₁≡ s f₁ x xs ys zs ∀₁ ≡₀ all₁ dsj | no f₁∉  = trans ≡₁ (trans (∀₁ f₁) ≡₂)
  where ≡₁ : exec s (xs ∷ʳ x) f₁ ≡ exec s xs f₁
        ≡₁ = sym (trans (St.lemma3 {exec s xs} f₁ (proj₂ (proj₁ (oracle x) (exec s xs))) f₁∉)
                        (cong-app (exec-∷ʳ s x xs) f₁))
        f₁∉₁ : f₁ ∉ Cwrites (exec s ys) x
        f₁∉₁ = subst (λ x₁ → f₁ ∉ map proj₁ (proj₂ x₁)) ≡₀ f₁∉
        ≡₂ : exec s (ys ++ zs) f₁ ≡ exec s (ys ++ x ∷ zs) f₁
        ≡₂ with exec-∷≡ f₁ (exec s ys) (run oracle x (exec s ys)) zs all₁ (St.lemma3 {exec s ys} f₁ (proj₂ (proj₁ (oracle x) (exec s ys))) f₁∉₁)
        ... | a = trans (cong-app (exec≡₄ {s} ys zs) f₁) (trans a (cong-app (exec≡₅ {s} x ys zs) f₁))
-- prove exec s (xs ∷ x) f₁ ≡ exec s xs f₁ ≡ exec s (ys ++ zs) f₁ ≡ exec s (xs ++ x ∷ ys) f₁

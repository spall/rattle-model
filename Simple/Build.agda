module Build where

open import Agda.Builtin.Equality
open import Cmd using (Cmd ; DisjointFiles ; outputFileNames ; inputFileNames ; run ; _Cmd-≟_) renaming (lemma2 to Cmd-lemma2 ; lemma1-1 to Cmd-lemma1-1)
open import Data.List using (List ; _++_ ; foldr ; [] ; _∷_ ; foldl)
open import Data.List.Membership.DecSetoid as ListMemDS
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Data.List.Membership.Setoid.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (tail ; head ; here ; there)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.Maybe using (just)
open import Data.Product using (_,_ ; ∃-syntax ; _×_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-decSetoid ; _×ₛ_ ; ×-decidable)
open import Data.String using (String ; _≟_ ; _==_)
open import Data.String.Properties using (≡-decSetoid ; ≡-setoid)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import File using (FileName ; Files ; fileNames ; File)
open import Relation.Binary.PropositionalEquality using (trans ; inspect ; sym ; subst ; cong ; setoid)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import State using (State ; extend)

open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_ ; ↭-trans ; ↭-sym )
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (++⁺ˡ ; shifts ; ∈-resp-↭)
open import Data.List.Relation.Binary.Pointwise using (_∷_ ; Pointwise-≡⇒≡)

open import Data.List.Membership.Setoid as ListMemS hiding (_∈_ ; _∉_)
module B = ListMemS (setoid Cmd)
open B using (_∈_)

module D = ListMemDS (×-decSetoid ≡-decSetoid ≡-decSetoid)
open D using (_∈?_)


Build : Set
Build = List Cmd

data HazardFree : Build -> List String -> Set where
  Null : {l : List String} -> HazardFree [] l -- empty build writes to nothing
  Cons : (c : Cmd) -> (b : Build) -> (l : List FileName) -> DisjointFiles c -> Disjoint (outputFileNames c) l -> HazardFree b ((outputFileNames c) ++ (inputFileNames c) ++ l) -> HazardFree (c ∷ b) l


exec : State -> Build -> State
exec st [] = st
exec st (x ∷ xs) = exec (run x st) xs

writes : Build -> List FileName
writes [] = []
writes (x ∷ b) = (outputFileNames x) ++ writes b


lemma1 : (s : FileName) -> (b : Build) -> s Cmd.A.∉ writes b -> ∀ st -> st s ≡ exec st b s
lemma1 s [] p = λ st → refl
lemma1 s (x ∷ b) p with lemma1 s b (λ x₁ -> p (∈-++⁺ʳ (outputFileNames x) x₁)) | Cmd-lemma2 x s λ x₁ -> p (∈-++⁺ˡ x₁)
... | f | f₂ = λ st → trans (f₂ st) (f (run x st))
          

lemma2-3 : {ls : List String} -> (s : FileName) -> (b : Build) -> s Cmd.A.∈ ls -> HazardFree b ls -> s Cmd.A.∉ writes b
lemma2-3 s .[] p2 Null = λ ()
lemma2-3 s .(c ∷ b) p2 (Cons c b ls _ x₁ p) with s Cmd.A.∈? outputFileNames c
... | yes p1 = λ x₂ → x₁ (p1 , p2)
... | no ¬p1 with lemma2-3 s b (∈-++⁺ʳ (outputFileNames c) (∈-++⁺ʳ (inputFileNames c) p2)) p
... | a = λ x₂ → a (f c b x₂ ¬p1)
  where f : (c : Cmd) -> (b : Build) -> s Cmd.A.∈ outputFileNames c ++ writes b -> s Cmd.A.∉ outputFileNames c -> s Cmd.A.∈ writes b
        f c b p p2 with ∈-++⁻ ≡-setoid (outputFileNames c) p
        ... | inj₁ i₁ = contradiction i₁ p2
        ... | inj₂ i₂ = i₂


lemma2-2 : (s : FileName) -> (x : Cmd) -> s Cmd.A.∈ outputFileNames x -> ∃[ v ](∀ st -> run x st s ≡ just v)
lemma2-2 s x p = f (Cmd.outputs x) p
  where f : (ls : Files) -> s Cmd.A.∈ fileNames ls -> ∃[ v ](∀ st -> foldr extend st ls s ≡ just v)
        f ((s₁ , v₁) ∷ ls) p with s₁ ≟ s | inspect (_==_ s₁) s
        ... | yes s₁≡s | b = v₁ , λ st → refl
        ... | no ¬s₁≡s | b = f ls (tail (λ s≡s₁ → ¬s₁≡s (sym s≡s₁)) p)


lemma2-1 : {ls : List String} (s : FileName) -> (b : Build) -> HazardFree b ls -> s Cmd.A.∈ writes b -> ∃[ v ](∀ st -> exec st b s ≡ just v)
lemma2-1 s (x ∷ b) (Cons .x .b _ x₁ x₂ p₁) p₂ with s Cmd.A.∈? outputFileNames x
... | yes p with lemma2-2 s x p
... | v , f with lemma1 s b (lemma2-3 s b (∈-++⁺ˡ p) p₁)
... | f₁ = v , λ st → trans (sym (f₁ (run x st))) (f st)
lemma2-1 s (x ∷ b) (Cons .x .b _ x₁ x₂ p₁) p₂ | no ¬p with ∈-++⁻ ≡-setoid (outputFileNames x) p₂
... | inj₁ y = contradiction y ¬p
... | inj₂ y with lemma2-1 s b p₁ y
... | v , f = v , λ st → f (run x st)


lemma2 : (s : FileName) -> (b : Build) -> HazardFree b [] -> s Cmd.A.∈ writes b -> ∀ st -> exec st b s ≡ exec (exec st b) b s
lemma2 s b p₁ p₂ with lemma2-1 s b p₁ p₂
... | v , f = λ st → trans (f st) (sym (f (exec st b)))


{- build is idempotent -}
build-idempotent : (b : Build) -> HazardFree b [] -> ∀ x st -> (exec st b) x ≡ (exec (exec st b) b) x
build-idempotent b p = λ x -> helper x
  where helper : (s : FileName) -> ∀ st -> (exec st b) s ≡ (exec (exec st b) b) s
        helper s with s Cmd.A.∈? writes b
        ... | yes x = lemma2 s b p x
        ... | no x = λ st → lemma1 s b x (exec st b)


lemma3 : {b : Build} {b₁ : Build} -> b ↭ b₁ -> writes b ↭ writes b₁
lemma3 _↭_.refl = _↭_.refl
lemma3 (_↭_.prep x p) = ++⁺ˡ (outputFileNames x) (lemma3 p)
lemma3 {x ∷ y ∷ xs} {y ∷ x ∷ ys} (_↭_.swap x y p) with lemma3 p
... | a with ++⁺ˡ (outputFileNames x) (++⁺ˡ (outputFileNames y) a)
... | a3 = ↭-trans a3 (shifts (outputFileNames x) (outputFileNames y))
lemma3 (_↭_.trans p p₁) = ↭-trans (lemma3 p) (lemma3 p₁)


lemma4-1 : {s : FileName} (b : Build) -> (x : Cmd) -> s Cmd.A.∈ writes (x ∷ b) -> s Cmd.A.∉ outputFileNames x -> s Cmd.A.∈ writes b
lemma4-1 _ x p₁ p₂ with ∈-++⁻ ≡-setoid (outputFileNames x) p₁
... | inj₁ x₁ = contradiction x₁ p₂
... | inj₂ y = y


lemma6 : {ls : List String} (s : FileName) -> (b : Build) -> HazardFree b ls -> (v : String) -> ∃[ x ](x B.∈ b × s Cmd.A.∈ outputFileNames x × ∀ st -> run x st s ≡ just v) -> ∀ st -> exec st b s ≡ just v
lemma6 s .(c ∷ b) (Cons c b _ x x₁ p₁) v (x₂ , x₂∈c∷b , s∈x₂ , f) with x₂ Cmd-≟ c
... | yes x₂≡c with lemma1 s b (lemma2-3 s b (∈-++⁺ˡ (subst (λ x₃ → s Cmd.A.∈ (outputFileNames x₃)) x₂≡c s∈x₂)) p₁)
... | a = λ st → trans (sym (a (run c st))) (subst (λ x₃ → run x₃ st s ≡ just v) x₂≡c (f st))
lemma6 s .(c ∷ b) (Cons c b _ x x₁ p₁) v (x₂ , x₂∈c∷b , s∈x₂ , f) | no ¬x₂≡c with lemma6 s b p₁ v (x₂ , (tail ¬x₂≡c x₂∈c∷b , s∈x₂ , f))
... | g = λ st → g (run c st)


lemma5 : (s : FileName) -> (b : Build) -> (b₁ : Build) -> s Cmd.A.∈ writes b -> b ↭ b₁ -> ∃[ x ](x B.∈ b × x B.∈ b₁ × s Cmd.A.∈ outputFileNames x × ∃[ v ](∀ st -> run x st s ≡ just v))
lemma5 s b b₁ p₁ p₂ = h p₂ (f s b p₁)
  where f : (s : FileName) -> (b : Build) -> s Cmd.A.∈ writes b -> ∃[ x ](x B.∈ b × s Cmd.A.∈ outputFileNames x × ∃[ v ](∀ st -> run x st s ≡ just v))
        f s (x ∷ b) p with s Cmd.A.∈? outputFileNames x
        ... | yes proof with lemma2-2 s x proof
        ... | v , g = x , here refl , proof , v , g
        f s (x ∷ b) p | no ¬proof with ∈-++⁻ ≡-setoid (outputFileNames x) p
        ... | inj₁ x₁ = contradiction x₁ ¬proof
        ... | inj₂ y with f s b y
        ... | cmd , fst₁ , v , snd = cmd , (there fst₁) , v , snd
        h : b ↭ b₁ -> ∃[ x ](x B.∈ b × s Cmd.A.∈ outputFileNames x × ∃[ v ](∀ st -> run x st s ≡ just v)) -> ∃[ x ](x B.∈ b × x B.∈ b₁ × s Cmd.A.∈ outputFileNames x ×  ∃[ v ](∀ st -> run x st s ≡ just v))
        h p₁ (x , fst , snd) = x , (fst , ∈-resp-↭ p₁ fst , snd)


lemma4 : (s : FileName) -> (b : Build) -> (b₁ : Build) -> b ↭ b₁ -> HazardFree b [] -> HazardFree b₁ [] -> s Cmd.A.∈ writes b -> s Cmd.A.∈ writes b₁ -> ∃[ v ](∀ st -> exec st b s ≡ just v × exec st b₁ s ≡ just v)
lemma4 s b b₁ p₁ p₂ p₃ p₄ p₅ with lemma5 s b b₁ p₄ p₁
... | x , fst , fst₁ , fst₂ , v , f with lemma6 s b p₂ v (x , fst , (fst₂ , f)) | lemma6 s b₁ p₃ v (x , (fst₁ , fst₂ , f))
... | a₁ | a₂ = v , (λ st → a₁ st , a₂ st)


{- exec st b s ≡ just v => ∃[ cmd ](cmd ∈ b × cmd ∈ b₁ × run cmd st s ≡ just v)
 => exec st b₁ s ≡ just v
-}

build-reordered : (b : Build) -> (b2 : Build) -> b ↭ b2 -> HazardFree b [] -> HazardFree b2 [] -> ∀ x st -> exec st b x ≡ exec st b2 x
build-reordered b b₁ p p1 p2 = λ x → helper x
  where helper : (s : FileName) -> ∀ st -> exec st b s ≡ exec st b₁ s
        helper s with s Cmd.A.∈? writes b
        ... | no ¬p₁ = λ st → trans (sym (lemma1 s b ¬p₁ st))
                                     (lemma1 s b₁ (λ x → ¬p₁ (∈-resp-↭ (↭-sym (lemma3 p)) x)) st)
        ... | yes p₁ with lemma4 s b b₁ p p1 p2 p₁ (∈-resp-↭ (lemma3 p) p₁)
        ... | v , f = λ st → trans (proj₁ (f st)) (sym (proj₂ (f st)))

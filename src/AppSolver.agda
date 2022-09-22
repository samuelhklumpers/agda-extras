{-# OPTIONS --safe #-}

module AppSolver where

open import Level renaming (zero to lzero; suc to lsuc)
open import Function.Base using (_$′_; _∘′_; id; _on_)
open import Data.Nat renaming (_⊔_ to _⊔ⁿ_)
open import Data.Product hiding (zip)
open import Data.Product.Relation.Binary.Lex.Strict
open import Induction.Lexicographic
open import Data.Sum
open import Induction
open import Induction.WellFounded as WF
open import Relation.Binary.PropositionalEquality renaming ([_] to [≡_]) hiding (inspect)
open import Data.Nat.Induction as N
open import Data.Nat.Properties
open import Data.Empty.Polymorphic
open import Relation.Binary.Construct.On
open import Data.Unit.Polymorphic
open import Cong-Skeletons
open import Relation.Binary
open import Relation.Binary.Indexed.Homogeneous hiding (Transitive)
open import Relation.Unary.Indexed
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Properties using () renaming (isEquivalence to isEquivalence-≡)


open import Applicatives

open ≡-Reasoning


private
  variable
    a b : Level

--* Intermediate datastructures
data AppRep {a} (F : Set a → Set a) (A : Set a) : Set (lsuc a) where
  Pure : A → AppRep F A
  Raw  : F A → AppRep F A
  _◯_  : {B : Set a} → AppRep F (B → A) → AppRep F B → AppRep F A

apR : ∀ {a} {F : Set a → Set a} {A B : Set a} → AppRep F (B → A) → AppRep F B → AppRep F A
apR = _◯_

data FreeAL {a} (F : Set a → Set a) (A : Set a) : Set (lsuc a) where
  PureL : A → FreeAL F A
  _:*:_ : {B : Set a} → FreeAL F (B → A) → F B → FreeAL F A


data Zip {a} (F : Set a → Set a) (A : Set a) : Set (lsuc a)
data Tail {a} (F : Set a → Set a) (A : Set a) : Set a → Set (lsuc a)  

data Tail {a} F A where
  none : Tail F A A
  tail : {C B : Set a} → F B → Tail F A (B → C) → Tail F A C

data Zip {a} F A where
  unZip : {C B : Set a} → Zip F (C → B) → FreeAL F C → Tail F B A → Zip F A
  done  : FreeAL F A → Zip F A

unTail : ∀ {A B} {F : Set a → Set a} → Tail F A B → FreeAL F A → FreeAL F B
unTail none u = u
unTail (tail x t) u = unTail t u :*: x


--* Conversion from intermediate structure to terms
module _ {a : Level} {F : Set a → Set a} (F' : RawApplicative F) where
  private
    open module X = RawIApplicative F' renaming (pure to pureF; ap to apF)
    
    variable
      A B C : Set a

  evalRep : AppRep F A → F A
  evalRep (Pure x) = pureF x
  evalRep (Raw x) = x
  evalRep (r ◯ s) = apF (evalRep r) (evalRep s)

  runFreeAL : FreeAL F A → F A
  runFreeAL (PureL x) = pureF x
  runFreeAL (r :*: x) = apF (runFreeAL r) x

  runTail : Tail F A B → F A → F B
  runTail none       u = u
  runTail (tail v t) u = apF (runTail t u) v

  tail-lemma : (u : FreeAL F A) → (t : Tail F A B) → runFreeAL (unTail t u) ≡ runTail t (runFreeAL u)
  tail-lemma u none       = refl
  tail-lemma u (tail x t) = apF ≡[ tail-lemma u t ] x

  runZip : Zip F A → F A
  runZip (unZip u v t) = runTail t (apF (runZip u) (runFreeAL v))
  runZip (done x)      = runFreeAL x


--* Proof of Zip-induction
HREL : ∀ {p a b} {I : Set p} → (I → Set a) → (I → Set b) → (ℓ : Level) → Set (p ⊔ a ⊔ b ⊔ lsuc ℓ)
HREL A B ℓ = ∀ i j → REL (A i) (B j) ℓ


data IAcc {p} {I : Set p} {a} {b} {F : I → Set a} (i : I) (cmp : HREL F F b) (x : F i) : Set (p ⊔ a ⊔ b) where
  acc : (rs : ∀ j (y : F j) → cmp j i y x → IAcc j cmp y) → IAcc i cmp x

IWellFounded : ∀ {p} {I : Set p} {a} {b} {F : I → Set a} → HREL F F b → Set _
IWellFounded cmp = ∀ i x → IAcc i cmp x

ITransitive : ∀ {p} {I : Set p} {a} {b} {F : I → Set a} → HREL F F b → Set _
ITransitive cmp = ∀ {i x j y k z} → cmp i j x y → cmp j k y z → cmp i k x z

ion : ∀ {p a b c} {I : Set p} {A : Set b} {F : I → Set a} → (∼ : Rel A c) → (f : ∀ j → F j → A) → HREL F F c
ion ∼ f i j a b = ∼ (f i a) (f j b)

ion-accessible : ∀ {p a b c} {I : Set p} {A : Set b} {F : I → Set a} {∼ : Rel A c} {i : I} {x : F i} {f : ∀ j → F j → A} → Acc ∼ (f i x) → IAcc i (ion ∼ f) x
ion-accessible {f = f} (acc rs) = acc (λ j y fy<fx → ion-accessible (rs (f j y) fy<fx))

ion-wf : ∀ {p a b c} {I : Set p} {A : Set b} {F : I → Set a} {∼ : Rel A c} {f : ∀ j → F j → A} → WellFounded ∼ → IWellFounded (ion ∼ f)
ion-wf {f = f} wf i x = ion-accessible (wf (f i x))

ion-trans : ∀ {p a b c} {I : Set p} {A : Set b} {F : I → Set a} {∼ : Rel A c} {f : ∀ j → F j → A} → Transitive ∼ → ITransitive (ion ∼ f)
ion-trans t = t

0,n<n,sm : ∀ n m → 1 ≤ n ⊎ Σ (0 ≡ n) (λ x → suc n ≤ suc m)
0,n<n,sm zero    m = inj₂ (refl , s≤s z≤n)
0,n<n,sm (suc n) m = inj₁ (s≤s z≤n)

_<<_ = ×-Lex _≡_ _<_ _<_


open import Relation.Binary.Reasoning.Preorder ≤-preorder renaming (begin_ to ≤-begin_; _∎ to _≤-∎) hiding (step-≡; step-≡˘)

module _ where
  <<-wf = ×-wellFounded <-wellFounded <-wellFounded

  open WF.All <<-wf lzero renaming (wfRec to ×-rec)

  private  
    go : (x : ℕ × ℕ) → ((y : ℕ × ℕ) → y << x → ℕ) → ℕ
    go (n     , suc m) r = 2 + (1 + (r (0 , n) (0,n<n,sm n m)) + r (n , m) (inj₂ (refl , ≤-refl)))
    go (0     , 0)     _ = 1
    go (suc n , 0)     r = 2 + r (0 , n) (inj₁ (s≤s z≤n))

  zip-height : ℕ × ℕ → ℕ
  zip-height x = ×-rec (λ _ → ℕ) go x

  go-ext : (x : ℕ × ℕ) {IH IH′ : WfRec _<<_ (λ _ → ℕ) x} → ({y : ℕ × ℕ} (y<x : y << x) → IH y y<x ≡ IH′ y y<x) → go x IH ≡ go x IH′
  go-ext (n     , suc m) {IH = a} {IH′ = b} h rewrite h {0 , n} (0,n<n,sm n m) | h {n , m} (inj₂ (refl , ≤-refl)) = refl
  go-ext (0     , 0)     {IH = a} {IH′ = b} h = refl
  go-ext (suc n , 0)     {IH = a} {IH′ = b} h rewrite h {0 , n} (inj₁ (s≤s z≤n))= refl

  open WF.FixPoint <<-wf (λ _ → ℕ) go go-ext

  zip-height-1 : (n m : ℕ) → zip-height (n , suc m) ≡ 3 + zip-height (0 , n) + zip-height (n , m)
  zip-height-1 n m = begin
    zip-height (n , suc m) ≡⟨ unfold-wfRec {(n , suc m)} ⟩
    3 + zip-height (0 , n) + zip-height (n , m) ∎

  zip-height-2 : (n : ℕ) → zip-height (suc n , 0) ≡ 2 + zip-height (0 , n)
  zip-height-2 n = unfold-wfRec {(suc n , 0)}


module _ {a : Level} {F : Set a → Set a} where
  private
    variable
      A B C D : Set a

  length : FreeAL F A → ℕ
  length (PureL x) = 0
  length (u :*: _) = suc (length u)

  tailLength : Tail F A B → ℕ
  tailLength none       = 0
  tailLength (tail _ t) = 1 + tailLength t

  length-unTail : (t : Tail F A B) → (u : FreeAL F A) → length (unTail t u) ≡ length u + tailLength t
  length-unTail none u = sym (+-identityʳ _)
  length-unTail (tail x t) u = trans (cong suc (length-unTail t u)) (sym (+-suc _ _))

  zipSize'' : Zip F A → ℕ
  zipSize'' (unZip z v t) = zipSize'' z + (length v + tailLength t)
  zipSize'' (done x)      = length x

  zip-step : FreeAL F (B → A) → FreeAL F B → Zip F A
  zip-step u         (v :*: w) = unZip (unZip (done (PureL _∘′_)) u none) v (tail w none)
  zip-step (PureL f) (PureL y) = done (PureL (f y))
  zip-step (u :*: v) (PureL y) = unZip (done (PureL (_∘′_ (_$′ y)))) u (tail v none)

  zip-step-size : (u : FreeAL F (B → A)) → (v : FreeAL F B) → zipSize'' (zip-step u v) ≡ length u + length v
  zip-step-size u         (v :*: w) rewrite +-identityʳ (length u) | +-comm 1 (length v) = refl
  zip-step-size (PureL f) (PureL y) = refl
  zip-step-size (u :*: v) (PureL y) rewrite +-suc (length u) 0 = refl 

  zip-steps : (A : Set a) → Zip F A → ℕ
  zip-steps _ (unZip z v t) = 1 + (zip-steps _ z + zip-height (zipSize'' z , length v))
  zip-steps _ (done _) = 0

  zip-steps' : Zip F A → ℕ
  zip-steps' = zip-steps _

  cmpZip : HREL (Zip F) (Zip F) lzero
  cmpZip = ion _<_ zip-steps
  
  _≺_ : Zip F A → Zip F B → Set
  _≺_ = cmpZip _ _
  
  ≺-wf : IWellFounded cmpZip
  ≺-wf i x = ion-wf <-wellFounded i x 

  _≼_ : Zip F A → Zip F B → Set
  u ≼ v = u ≺ v ⊎ zip-steps' u ≡ zip-steps' v

  z≺unZip : ∀ {A B C} → (z : Zip F (B → A)) (u : FreeAL F B) (t : Tail F A C) → z ≺ unZip z u t
  z≺unZip z u t = ≤-trans ≤-refl (s≤s (m≤m+n _ _))

  ≺-trans : ∀ {A B C} (x : Zip F A) (y : Zip F B) (z : Zip F C) → x ≺ y → y ≺ z → x ≺ z
  ≺-trans x y z p q = <-trans p q

  ≺≼ : ∀ {A B C} (x : Zip F A) (y : Zip F B) (z : Zip F C) → x ≺ y → y ≼ z → x ≺ z
  ≺≼ x y z p (inj₁ q) = ≺-trans x y z p q
  ≺≼ x y z p (inj₂ q) rewrite q = p

  zip-step-decreasing : (u : FreeAL F (B → A)) (v : FreeAL F B) → 1 + zip-steps' (zip-step u v) ≡ zip-height (length u , length v) 
  zip-step-decreasing u (_:*:_ {B = C} v w) = begin
    1 + zip-steps' (unZip (unZip (done (PureL _∘′_)) u none) v (tail w none)) ≡⟨ cong (λ k → (2 + (zip-steps _ (unZip (done (PureL (_∘′_ {A = C}))) u none)  + zip-height (k , length v)))) (+-identityʳ (length u)) ⟩
    2 + (1 + zip-height (0 , (length u)) + zip-height (length u , length v)) ≡˘⟨ zip-height-1 (length u) (length v) ⟩
    zip-height (length u , 1 + length v) ∎
  zip-step-decreasing (PureL f) (PureL y) = refl
  zip-step-decreasing (u :*: v) (PureL y) = begin
    1 + zip-steps' (zip-step (u :*: v) (PureL y)) ≡˘⟨ zip-height-2 (length u) ⟩
    zip-height (1 + length u , 0) ∎


-- need this to inspect a value _and_ keep it
-- (from the Agda wiki)
data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl


--* Theorem: simplify respects equality
module _ {a : Level} {F : Set a → Set a} (F'' : Applicative F) where
  private
    F' = F'' .rawIA
    
    open module X = RawIApplicative F' renaming (pure to pureF; ap to apF)
    
    variable
      A B C : Set a

  zip-step-≈ : (u : FreeAL F (B → A)) (v : FreeAL F B) → runZip F' (zip-step u v) ≡ apF (runFreeAL F' u) (runFreeAL F' v)
  zip-step-≈ u         (v :*: w) = a-comp F'' _ _ _
  zip-step-≈ (PureL f) (PureL y) = sym (hom F'' _ _)
  zip-step-≈ (u :*: v) (PureL y) = trans (trans (apF ≡[ apF ≡[ sym (hom F'' _ _) ] _ ] _) (a-comp F'' _ _ _)) (sym (inter F'' _ _)) 

  IRecursor : ∀ {p a b c : Level} {I : Set p} {F : I → Set a} → (∼ : HREL F F b) → Set (p ⊔ a ⊔ b ⊔ lsuc c)
  IRecursor {c = c} {F = F} ∼ = (P : IPred F c) → (∀ j → (y : F j) → (∀ k → (z : F k) → ∼ k j z y → P z) → P y) → ∀ i → (x : F i) → P x

  ≺-rec : ∀ {b} → IRecursor {c = b} {F = Zip F} cmpZip
  ≺-rec P f i x = f i x (builder P f i x (≺-wf i x))
    where
      builder : ∀ {b} → (P : IPred (Zip F) b)
              → (∀ B → (y : Zip F B) → (∀ C → (z : Zip F C) → z ≺ y → P z) → P y) → ∀ A → (x : Zip F A)
              → IAcc A cmpZip x → ∀ D → (w : Zip F D) → w ≺ x → P w
      builder P f A x (acc rs) = λ D w w≺x → f D w (builder P f D w (rs D w w≺x))

  zip : ∀ {A} → (u : FreeAL F (B → A)) (v : FreeAL F B) → Σ (FreeAL F A) λ w → runFreeAL F' w ≡ apF (runFreeAL F' u) (runFreeAL F' v)
  zip {A = A} u' v' = let (w , p , _) = ≺-rec Go go A (unZip (done u') v' none) in (w , p)
    where
      Go : ∀ {A} → Zip F A → Set (lsuc a)
      Go {A = A} z = Σ (FreeAL F A) λ w → (runFreeAL F' w ≡ runZip F' z × length w ≡ zipSize'' z)

      -- quadratic
      go : ∀ B → (x : Zip F B) → (∀ C → (y : Zip F C) → y ≺ x → Go y) → Go x
      go _ (done u)      _   = u , refl , refl
      go _ (unZip z v t) r   with r _ z (z≺unZip z v t)
      ... | a , b , c with inspect (zip-step a v)
      ... | done u with≡ x = unTail t u , (
        begin
          runFreeAL F' (unTail t u) ≡⟨ tail-lemma F' u t ⟩
          runTail F' t ≡[ begin
            runZip F' ≡[ sym x ⟩
            runZip F' (zip-step a v) ≡⟨ zip-step-≈ a v ⟩
            apF ≡[ b ] (runFreeAL F' v) ⟩
            apF (runZip F' z) (runFreeAL F' v) ∎ ⟩
          runTail F' t (apF (runZip F' z) (runFreeAL F' v))  ∎
        ) , (
        begin
          length (unTail t u) ≡⟨ length-unTail t u ⟩
          _+_ ≡[ zipSize'' ≡[ sym x > ] tailLength t ⟩
          _+_ ≡[ zip-step-size a v ] tailLength t ⟩
          (length a + length v) + tailLength t ≡⟨ +-assoc (length a) (length v) (tailLength t) ⟩
          _+_ ≡[ c ] (length v + tailLength t) ⟩
          zipSize'' z + (length v + tailLength t) ∎)
      ... | k@(unZip z' v' t') with≡ x with r _ k (
        ≤-begin
          1 + zip-steps' k ≈⟨ cong (λ p → 1 + zip-steps' p) (sym x) ⟩
          1 + zip-steps' (zip-step a v) ≈⟨ zip-step-decreasing a v ⟩
          zip-height (length a , length v) ∼⟨ m≤n+m (zip-height (length a , length v)) (1 + zip-steps' z) ⟩
          1 + zip-steps' z + zip-height (length a , length v)  ≈⟨ cong (λ p → 1 + zip-steps' z + zip-height (p , length v)) c ⟩
          1 + zip-steps' z + zip-height (zipSize'' z , length v) ≤-∎)
      ... | d , e , f = unTail t d , (
        begin 
          runFreeAL F' (unTail t d) ≡⟨ tail-lemma F' d t ⟩
          runTail F' t ≡[ begin 
            runFreeAL F' d ≡⟨ e ⟩
            runZip F' k ≡⟨ cong (runZip F') (sym x) ⟩
            runZip F' (zip-step a v) ≡⟨ zip-step-≈ a v ⟩
            apF ≡[ b ] (runFreeAL F' v) ⟩
            apF (runZip F' z) (runFreeAL F' v) ∎ ⟩
          runZip F' (unZip z v t) ∎) , (
        begin
          length (unTail t d) ≡⟨ length-unTail t d ⟩
          _+_ ≡[ f ] tailLength t ⟩
          _+_ ≡[ zipSize'' ≡[ sym x > ] tailLength t  ⟩
          _+_ ≡[ zip-step-size a v ] tailLength t ⟩
          (length a + length v) + tailLength t ≡⟨ +-assoc (length a) (length v) (tailLength t) ⟩
          _+_ ≡[ c ] (length v + tailLength t) ⟩
          zipSize'' z + (length v + tailLength t) ∎)

  simplify : (rep : AppRep F A) → Σ (FreeAL F A) (λ u → evalRep F' rep ≡ runFreeAL F' u)
  simplify (Pure x) = PureL x , refl
  simplify (Raw f)  = PureL id :*: f , sym (a-ident F'' f)
  simplify (u ◯ v)  with simplify u | simplify v
  ... | (w , p) | (x , q) with zip w x
  ... | (y , r) = y , trans (cong₂ apF p q) (sym r)


-- todo put simplify in a macro

{-
--* Temporary tests
open import Data.Extra.Identity

-- simplify completely breaks C-c C-d
module Test {u v : Identity {lzero} (⊤ → ⊤ → ⊤)} {w x : Identity {lzero} (⊤ → ⊤)} {y z : Identity {lzero} ⊤} where
  test' : AppRep {lzero} Identity ⊤
  test' = (Raw u ◯ Raw y) ◯ (Raw w ◯ Raw z)
  test'' = proj₁ (simplify IdA test')
  test''' : AppRep {lzero} Identity ⊤
  test''' = Raw x ◯ Pure tt
  test'''' = proj₁ (simplify IdA test''')

  open RawIApplicative (IdRawA {lzero}) renaming (pure to pureI; ap to apI)

  the-eq : apI x (pureI tt) ≡ apI (pureI (_$′ tt)) x
  the-eq = proj₂ (simplify IdA test''')

  the-eq-2 : apI (apI u y) (apI w z) ≡ runFreeAL IdRawA (proj₁ (simplify IdA test'))
  the-eq-2 = proj₂ (simplify IdA test')
  

open Test public
-}

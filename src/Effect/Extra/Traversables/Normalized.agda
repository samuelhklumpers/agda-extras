{-# OPTIONS --cubical-compatible #-}

-- refer to: https://github.com/pigworker/SSGEP-DataData/blob/master/NormT.lagda
-- see: https://stackoverflow.com/a/32821966/5895919

module Effect.Extra.Traversables.Normalized where


open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Data.Product.Properties
open import Data.Unit
open import Function.Base
open import Data.Nat.Base hiding (_⊔_)
open import Data.Nat.Properties
open import Data.List.Base
open import Data.List.Properties
open import Data.Vec.Base hiding (length)
open import Relation.Binary.PropositionalEquality
open import Data.Empty

data Normal (Shape : Set) (size : Shape → ℕ) (A : Set) : Set where
  --_▷_ : (S : Shape) → Vec A (size S) 

-- Example

-- postulate Traversable ≅ Normal

-- prove foldT ≡ foldList ∘ toList
-- traverse (g ◦ h) = traverse g ◦ fmap h
-- (g : T B → C) (f : A → B) → g (fmap f x) ≡ g x → Σ[ h ∈ T ⊤ → C ] h (fmap (const tt) x) ≡ g x 


{-

open ≡-Reasoning

open import Data.Extra.Compose
open import Data.Extra.Compose.Instances
open import Data.Extra.Const
open import Data.Extra.Const.Instances
open import Data.Extra.Identity
open import Data.Extra.Identity.Instances
open import Data.Extra.List.Instances
open import Data.Extra.Nat.Instances
open import Effect.Extra.Applicatives
open import Effect.Extra.Applicatives.Solver
open import Effect.Extra.Foldables renaming (length to lengthT)
open import Effect.Extra.Traversables
open import Structures.Monoids
open import Misc.Cong-Reasoning
open import Extensionality


open import Function.Inverse hiding (sym; id)
open Inverse


Inv : ∀ f t → Set f → Set t → Set (f ⊔ t)
Inv f t = _↔_ {f} {t}

-- TODO implement Traversable Normal

private
  variable 
    a b c d : Level


data Normal (Shape : ℕ → Set a) (A : Set b) : Set (a ⊔ b) where
  normal : ∀ {n} → Shape n → (xs : List A) → length xs ≡ n → Normal Shape A


module Normalize (F : Set → Set) (T : Traversable F) where
  private
    open module TF {a} = RawTraversable {b = a} (T .rawT) renaming (traverse to trav)

  TFold : ∀ {b} → Foldable {c = b} F 
  TFold = rawTTFold (T .rawT)

  TFun : Functor F
  TFun = TTF T

  TRawFun : RawFunctor F
  TRawFun = TFun .rawF

  data ShapeSize : ℕ → Set where
    shape : (t : F ⊤) → ShapeSize (lengthT TFold t)

  shapeT : ∀ {A} → (t : F A) → Σ ℕ λ n → ShapeSize n
  shapeT t = let t' = fmap TRawFun (λ _ → tt) t in
    lengthT TFold t' , (shape t')

  contentT : ∀ {A} → (t : F A) → List A
  contentT t = foldMap TFold ListMonoid (_∷ []) t

  compA : {G : Set b → Set c} {F : Set a → Set b} → Applicative G → Applicative F → Applicative (G ∘′ F)
  compA G F = record
    { rawIA = compRawA (G .rawIA) (F .rawIA)
    ; a-ident = λ v → trans (simplify G) (trans (cong (λ k → apG (pureG k) v) (f-ext (a-ident F))) (a-ident G v))
    ; a-comp = λ u v w → begin (
      _ ≡⟨ simplify G ⟩
      apG ≡[ apG ≡[ apG ≡[ pureG ≡[ f-ext (λ x → f-ext (λ y → f-ext (λ z → a-comp F x y z))) > ] u ] v ] w ⟩
      _ ≡˘⟨ simplify G ⟩
      _ ∎
      )
    ; hom = λ f x → trans (simplify G) (cong pureG (hom F f x))
    ; inter = λ u y → trans (simplify G) (cong (λ k → apG k u) (trans (cong pureG (f-ext (λ v → inter F v y) )) (sym (simplify G)))) }
    where
      open module X = RawIApplicative (G .rawIA) renaming (ap to apG; pure to pureG)


  length-hom : {A : Set a} → MonoidHom (ListMonoid {A = A}) ℕ-+-M length
  length-hom = record { m-neutral = refl ; m-mappend = λ xs _ → length-++ xs }

  MonoidHom⇒AppTrans : ∀ {b} {M₀ N₀ : Set a} (M : Monoid M₀) (N : Monoid N₀) → (mor : M₀ → N₀) → MonoidHom M N mor → AppTrans {a = b} (constA M) (constA N) mor
  MonoidHom⇒AppTrans M N mor hom = record { t-pure = λ _ → hom .m-neutral ; t-ap = λ x f → hom .m-mappend f x }

  shape-length : ∀ {A} → (t : F A) → length (contentT t) ≡ proj₁ (shapeT t)
  shape-length t = begin
    length (contentT t) ≡⟨ t-nat T length (_∷ []) (constA ListMonoid) (constA ℕ-+-M) (MonoidHom⇒AppTrans ListMonoid ℕ-+-M length length-hom) t ⟩
    lengthT TFold t ≡⟨ t-comp T (constA ℕ-+-M) idA (λ _ → 1) (λ _ → tt) t ⟩
    proj₁ (shapeT t) ∎

  shape-length' : ∀ {A} → (t : F A) → lengthT TFold t ≡ lengthT TFold (fmap TRawFun (const tt) t)
  shape-length' t = t-comp T (constA ℕ-+-M) idA (λ _ → 1) (λ _ → tt) t

  toNormal : ∀ {A} → F A → Normal ShapeSize A
  toNormal t = normal (proj₂ (shapeT t)) (contentT t) (shape-length t)
    
  Vec' : Set a → ℕ → Set a
  Vec' A n = Σ (List A) λ xs → length xs ≡ n

  Batch : Set a → Set a → Set a
  Batch A B = Σ ℕ λ n → (xs : Vec' A n) → B

  chop : {A : Set a} (m : ℕ) {n : ℕ} -> (xs : Vec' A (m + n)) -> Vec' A m × Vec' A n
  chop zero    (xs , p) = ([] , refl) , (xs , p)
  chop (suc m) (x ∷ xs , p) = let ((ys , q) , (zs , r)) = chop m (xs , suc-injective p) in
    (x ∷ ys , cong suc q) , (zs , r)

{-
  chop zero    ([]     , p) = {!!}
  chop (suc m) ([]     , p) = ⊥-elim (0≢1+n p)
  chop zero    (x ∷ xs , p) = {!!}
  --[] , xs
  chop (suc m) (x ∷ xs , p) = {!!}
  --let (ys , zs) = chop m xs in x ∷ ys , zs 
-}

  BatchRawA : {A : Set a} → RawApplicative (Batch A)
  BatchRawA = record
    { pure = λ x → 0 , (const x)
    ; ap   = λ { (n , f) (m , g) → n + m , λ xs → let (ys , zs) = chop n xs in f ys (g zs)  }
    }

  BatchA : {A : Set a} → Applicative (Batch A)
  BatchA = record
    { rawIA = BatchRawA
    ; a-ident = λ v → refl
    ; a-comp = λ u v w → {!!}
    ; hom = λ f x → refl
    ; inter = inter'
    } --  λ u y → Σ-≡,≡→≡ (+-identityʳ (proj₁ u) , {!refl!})
    where
      inter' : {A B C : Set a} (u : Batch A (B → C)) (y : B)
             → ap BatchRawA u (pure BatchRawA y) ≡ ap BatchRawA (pure BatchRawA (_$′ y)) u
      inter' u y = Σ-≡,≡→≡ (+-identityʳ (proj₁ u) , {!h!})
        where
        h : {A B C : Set a} {u : Batch A (B → C)} {y : B}
          → subst (λ n → Vec' A n → C) (+-identityʳ (proj₁ u)) (proj₂ (ap BatchRawA u (pure BatchRawA y))) ≡ proj₂ (ap BatchRawA (pure BatchRawA (_$′ y)) u)
        h with proj₁ u + 0 | proj₁ u | +-identityʳ (proj₁ u)
        ...| a | b | c = {!a b c!}
         


  batchSingl : {A : Set a} → Batch A A
  batchSingl = 1 , λ { (x ∷ [] , _) → x }

  shapeBatch : {A : Set} → F ⊤ → Batch A (F A)
  shapeBatch s = trav BatchRawA (const batchSingl) s

  proj₁-AT : {A : Set} → AppTrans (BatchA {A = A}) (constA ℕ-+-M) proj₁
  proj₁-AT = record
    { t-pure = λ _ → refl
    ; t-ap = λ _ _ → refl
    }
    
  shapeBatch-length : {A : Set} (s : F ⊤) → proj₁ (shapeBatch {A = A} s) ≡ lengthT TFold s
  shapeBatch-length {A = A} s = begin
    proj₁ (shapeBatch {A = A} s) ≡⟨ t-nat T proj₁ (const batchSingl) BatchA (constA ℕ-+-M) proj₁-AT s ⟩
    trav (constRawA ℕ-+-M) (const 1) s ≡⟨ t-comp T idA (constA ℕ-+-M) (λ ()) (const 1) s ⟩ -- McBride really comes up with these things that just inexplicably work ; TODO extract this to show the default Fold for Traversable is irrelevant in B
    trav (constRawA ℕ-+-M) (const 1) s ∎

  fromNormal : ∀ {A} → Normal ShapeSize A → F A
  fromNormal {A = A} (normal (shape s) xs p) = proj₂ (shapeBatch {A = A} s) (xs , (trans p (sym (shapeBatch-length s))))

  ≡-Normal : ∀ {n m} {A : Set a} (Shape : ℕ → Set a) → (s : Shape n) (t : Shape m) → (xs ys : List A) → (r : n ≡ m) (p : length xs ≡ n) → (q : length ys ≡ m) → subst Shape r s ≡ t → xs ≡ ys → normal {Shape = Shape} s xs p ≡ normal {Shape = Shape} t ys q 
  ≡-Normal S s .s xs .xs refl refl refl refl refl = refl

  fromNormal-contentT : ∀ {A n} → (s : ShapeSize n) (xs : List A) (p : length xs ≡ n) → contentT (fromNormal (normal s xs p)) ≡ xs
  fromNormal-contentT (shape t) xs p = {!!}

  Traversable≅Normal : ∀ {A} → F A ↔ Normal ShapeSize A
  Traversable≅Normal {A = A} = inverse toNormal fromNormal ret sec
    where
    lemma : ∀ {n} {A : Set} → (s : ShapeSize n) (xs : List A) (p : length xs ≡ n) → lengthT TFold (fmap TRawFun (λ _ → tt) (fromNormal (normal s xs p))) ≡ n
    lemma (shape t) xs p = begin
      lengthT TFold (fmap TRawFun (const tt) _) ≡˘⟨ shape-length' (fromNormal (normal (shape t) xs p)) ⟩
      lengthT TFold _ ≡⟨ {!!} ⟩
      lengthT TFold t ∎

    ret : (x : F A) → fromNormal (toNormal x) ≡ x
    ret = {!!}
    
    sec : (x : Normal ShapeSize A) → toNormal (fromNormal x) ≡ x
    sec x'@(normal {n} s xs p) = ≡-Normal ShapeSize (proj₂ (shapeT (fromNormal (normal s xs p)))) s (contentT (fromNormal (normal s xs p))) xs (lemma s xs p) (shape-length (fromNormal x')) p {!!} (fromNormal-contentT s xs p)
  
  -- TODO we can probably patch together the proofs by "batching the proof" along with the content

-}

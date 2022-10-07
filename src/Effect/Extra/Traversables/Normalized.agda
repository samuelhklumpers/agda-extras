-- refer to: https://github.com/pigworker/SSGEP-DataData/blob/master/NormT.lagda
-- see: https://stackoverflow.com/a/32821966/5895919

module Effect.Extra.Traversables.Normalized where

open import Level
open import Data.Product
open import Data.Unit
open import Function.Base
open import Data.Nat.Base hiding (_⊔_)
open import Data.List.Base
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality

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


open import Function.Inverse hiding (sym)
open Inverse


Inv : ∀ f t → Set f → Set t → Set (f ⊔ t)
Inv f t = _↔_ {f} {t}

-- TODO implement Traversable Normal

private
  variable 
    a b c : Level


data Normal (Shape : ℕ → Set a) (A : Set b) : Set (a ⊔ b) where
  normal : ∀ {n} → Shape n → (xs : List A) → length xs ≡ n → Normal Shape A


module Normalize (F : Set → Set) (T : Traversable F) where
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
    ; a-ident = {!!}
    ; a-comp = {!!}
    ; hom = {!!}
    ; inter = {!!} }

  constA : ∀ {A} → Monoid A → Applicative {a = a} {b = b} (const A)
  constA M = record
    { rawIA = constRawA M
    ; a-ident = {!!}
    ; a-comp = {!!}
    ; hom = {!!}
    ; inter = {!!} }

  length-hom : {A : Set a} → MonoidHom (ListMonoid {A = A}) ℕ-+-M length
  length-hom = record { m-neutral = refl ; m-mappend = λ xs _ → length-++ xs }

  MonoidHom⇒AppTrans : ∀ {b} {M₀ N₀ : Set a} (M : Monoid M₀) (N : Monoid N₀) → (mor : M₀ → N₀) → MonoidHom M N mor → AppTrans {a = b} (constA M) (constA N) mor
  MonoidHom⇒AppTrans M N mor hom = record { t-pure = λ _ → hom .m-neutral ; t-ap = λ x f → hom .m-mappend f x }
  
  toNormal : ∀ {A} → F A → Normal ShapeSize A
  toNormal t = normal (proj₂ (shapeT t)) (contentT t) (begin
    length (contentT t) ≡⟨ t-nat T length (_∷ []) (constA ListMonoid) (constA ℕ-+-M) (MonoidHom⇒AppTrans ListMonoid ℕ-+-M length length-hom) t ⟩
    lengthT TFold t ≡⟨ t-comp T (constA ℕ-+-M) idA (λ _ → 1) (λ _ → tt) t ⟩
    proj₁ (shapeT t) ∎)

  fromNormal : ∀ {A} → Normal ShapeSize A → F A
  fromNormal n = {!!}

  Traversable≅Normal : ∀ {A} → F A ↔ Normal ShapeSize A
  Traversable≅Normal = inverse toNormal fromNormal {!!} {!!}

{-# OPTIONS --without-K #-}

module Effect.Extra.Traversables where

open import Data.Unit
open import Data.Empty.Polymorphic
open import Function.Base using (id; _$′_; _∘′_; const)
open import Level
open import Relation.Binary.PropositionalEquality

open import Data.Extra.Compose
open import Data.Extra.Compose.Instances
open import Data.Extra.Const
open import Data.Extra.Const.Instances
open import Data.Extra.Function.Instances
open import Data.Extra.Identity
open import Data.Extra.Identity.Instances
open import Effect.Extra.Applicatives
open import Effect.Extra.Foldables
open import Structures.Monoids
open import Structures.Semigroups


open ≡-Reasoning


private
  variable
    a b c d : Level
    A B C D : Set a


record RawTraversable {b} (T : Set a → Set a) : Set (suc a ⊔ suc b) where
  field
    traverse : ∀ {A B} → {F : Set a → Set b} → RawApplicative F → (A → F B) → T A → F (T B)

open RawTraversable public

    
idRawA : RawApplicative {a = a} id
idRawA = record { pure = id ; ap = id }

idA : Applicative {a = a} id
idA = record
  { rawIA   = idRawA
  ; a-ident = λ v → refl
  ; a-comp  = λ u v w → refl
  ; hom     = λ f x → refl
  ; inter   = λ u y → refl }

compRawA : {G : Set b → Set c} {F : Set a → Set b} → RawApplicative G → RawApplicative F → RawApplicative (G ∘′ F)
compRawA G F = record { pure = λ x → pure G (pure F x) ; ap = λ f x → ap G (ap G (pure G (ap F)) f) x }
           
record Traversable {a} (T : Set a → Set a) : Setω where
  field
    rawT : RawTraversable {a = a} {b = b} T
 
    t-nat : {F' G' : Set a → Set b} (morph : F' ∹> G') (f : A → F' B)
            → (F : Applicative F') (G : Applicative G') → AppTrans F G morph
            → (x : T A) → morph (traverse rawT (F .rawIA) f x) ≡ traverse rawT (G .rawIA) (morph ∘′ f) x

    t-ident : (x : T A) → traverse rawT idRawA id x ≡ x

    t-comp : {A : Set a} {B : Set a} {C : Set a} {G' : Set a → Set a} {F' : Set a → Set a}
           → (G : Applicative G') (F : Applicative F')
           → (g : B → G' C) (f : A → F' B) (x : T A)
           → traverse rawT (compRawA (F .rawIA) (G .rawIA)) (fmap (rawATF (F .rawIA)) g ∘′ f) x ≡ fmap (rawATF (F .rawIA)) (traverse rawT (G .rawIA) g) (traverse rawT (F .rawIA) f x)

open Traversable public


module TravToFold {F : Set a → Set a} where
  rawTTFold : ∀ {b} → RawTraversable {b = b} F → Foldable {c = b} F
  rawTTFold {b = b} T = record { foldMap = λ M f xs → traverse T {B = ⊥} (constRawA M) f xs }

open TravToFold public

module TravToFun {a} {F : Set a → Set a} where
  rawTTF : RawTraversable {b = a} F → RawFunctor F
  rawTTF T = record { _<$>_ = traverse T idRawA }

  TTF : Traversable F → Functor F
  TTF T = record
    { rawF    = rawTTF (T .rawT)
    ; f-ident = t-ident T
    ; f-comp  = λ g f x → sym (t-comp T idA idA g f x)
    }

open TravToFun public

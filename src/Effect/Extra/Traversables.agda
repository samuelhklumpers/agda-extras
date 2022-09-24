{-# OPTIONS --without-K #-}

module Effect.Extra.Traversables where

open import Data.Unit
open import Data.Empty.Polymorphic
open import Function.Base using (id; _$′_; _∘′_)
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


private
  variable
    a b c : Level
    A B C : Set a


record RawTraversable {b} (T : Set a → Set a) : Set (suc a ⊔ suc b) where
  field
    traverse : {F : Set a → Set b} → RawApplicative F → (A → F B) → T A → F (T B)

open RawTraversable public

           
record Traversable (T : Set a → Set a) : Setω where
  field
    rawT : ∀ {b} → RawTraversable {b = b} T
 
    t-nat : {F' G' : Set a → Set b} (t : RawAppTrans F' G') (f : A → F' B)
            → (F : Applicative F') (G : Applicative G') → AppTrans t
            → (x : T A) → t F G (traverse rawT (F .rawIA) f x) ≡ traverse rawT (G .rawIA) (t F G ∘′ f) x
            
    t-ident : (x : T A) → traverse rawT IdRawA identity x ≡ identity x

    t-comp : {A : Set a} {B : Set a} {C : Set a} {F' : Set a → Set a} {G' : Set a → Set a}
      → (G : Applicative G') (F : Applicative F')
      → (g : B → G' C) (f : A → F' B) (x : T A)
      → traverse rawT (CompRawA (F .rawIA) (G .rawIA)) (λ y → compose (fmap (rawATF (F .rawIA)) g (f y))) x ≡ compose (fmap (rawATF (F .rawIA)) (traverse rawT (G .rawIA) g) (traverse rawT (F .rawIA) f x))

open Traversable public

 

{-# OPTIONS --without-K #-}

module Traversables where

open import Function.Base using (id; _$′_; _∘′_)
open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Empty.Polymorphic

open import Applicatives
open import Foldables
open import Data.Extra.Function
open import Data.Extra.Compose
open import Monoids
open import Data.Extra.Const
open import Data.Extra.Identity
open import Data.Extra.Compose.Instances

private
  variable
    a b c : Level
    A B C : Set a



record RawTraversable {b} (T : Set a → Set a) : Set (suc a ⊔ suc b) where
  field
    traverse : {F : Set a → Set b} → RawApplicative F → (A → F B) → T A → F (T B)

open RawTraversable public


AppTrans' : (Set a → Set b) → (Set a → Set c) → Set (suc a ⊔ b ⊔ c)
AppTrans' F G = ∀ {A} → Applicative F → Applicative G → F A → G A

record AppTrans {b} {F₀ G₀ : Set a → Set b} (t : AppTrans' F₀ G₀) : Set (suc a ⊔ suc b) where
  field
    t-pure : (F : Applicative F₀) (G : Applicative G₀) → (x : A) → t F G (pure (F .rawIA) x) ≡ pure (G .rawIA) x
    t-ap   : (F : Applicative F₀) (G : Applicative G₀) → (x : F₀ A) (f : F₀ (A → B))
           → t F G (ap (F .rawIA) f x) ≡ ap (G .rawIA) (t F G f) (t F G x)
           
open AppTrans public


record Traversable (T : Set a → Set a) : Setω where
  field
    rawT : ∀ {b} → RawTraversable {b = b} T
 
    t-nat : {F' G' : Set a → Set b} (t : AppTrans' F' G') (f : A → F' B) → (F : Applicative F') (G : Applicative G') → AppTrans t →
            (x : T A) → t F G (traverse rawT (F .rawIA) f x) ≡ traverse rawT (G .rawIA) (t F G ∘′ f) x
            
    t-ident : (x : T A) → traverse rawT IdRawA identity x ≡ identity x

    t-comp : {G' F' : Set a → Set a} → (G : Applicative G') (F : Applicative F') →
             (g : B → G' C) (f : A → F' B) (x : T A) →
             --traverse rawT (CompRawA (F .rawIA) (G .rawIA)) (compose ∘′ (fmap (rawATF (F .rawIA)) g ∘′ f)) x ≡ compose (fmap (rawATF (F .rawIA)) (traverse rawT (G .rawIA) g) (traverse rawT (F .rawIA) f x))
             traverse rawT (CompRawA (F .rawIA) (G .rawIA)) (λ y → compose (fmap (rawATF (F .rawIA)) g (f y))) x ≡ compose (fmap (rawATF (F .rawIA)) (traverse rawT (G .rawIA) g) (traverse rawT (F .rawIA) f x))

open Traversable public


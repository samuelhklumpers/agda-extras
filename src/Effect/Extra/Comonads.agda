{-# OPTIONS --without-K #-}

module Effect.Extra.Comonads where

open import Function.Base using (id; _$′_; _∘′_)
open import Effect.Functor using (RawFunctor)
open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Unit

open import Extensionality


private
  variable
    p a b : Level
    A B C : Set a


record RawComonad (W : Set a → Set b) : Set (suc a ⊔ b) where
  field
    extract : W A → A
    extend  : (W A → B) → W A → W B

record Comonad (W : Set a → Set b) : Set (suc a ⊔ b) where
  field
    rawW : RawComonad W

  private
    open module X = RawComonad rawW

  field
    id-left  : (w : W A)
      → (extend extract w) ≡ w
    id-right : (w : W A) (f : W A → B)
      → extract (extend f w) ≡ f w
    cossa    : (w : W A) (f : W A → B) (g : W B → C)
      → extend g (extend f w) ≡ extend (g ∘′ extend f) w


open Comonad public

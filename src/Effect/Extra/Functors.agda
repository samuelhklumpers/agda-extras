{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Extra.Functors where

open import Prelude
open import Effect.Functor using (RawFunctor) public


private
  variable
    a b : Level
    A B C : Set a

fmap : {F : Set a → Set b} → RawFunctor F → (A → B) → F A → F B
fmap F = F .RawFunctor._<$>_

record Functor (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  field 
    rawF : RawFunctor F

  private
    open module X = RawFunctor rawF

  field
    f-ident : (x : F A) → (id <$> x) ≡ x
    f-comp  : (g : B → C) (f : A → B) (x : F A)
          → (g <$> (f <$> x)) ≡ ((g ∘′ f) <$> x)

open Functor public

{-# OPTIONS --without-K --safe #-}

module Effect.Extra.Foldables where

open import Level

open import Structures.Monoids

private
  variable
    a b c : Level
    A : Set a

record Foldable {c} (T : Set a → Set b) : Set (suc a ⊔ b ⊔ suc c) where
  field
    foldMap : {M : Set c} → Monoid M → (A → M) → T A → M

open Foldable public

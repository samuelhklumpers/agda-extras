{-# OPTIONS --without-K --safe #-}

module Foldables where

open import Level

open import Monoids

private
  variable
    a b c : Level
    A : Set a

record Foldable {c} (T : Set a → Set b) : Set (suc a ⊔ b ⊔ suc c) where
  field
    foldMap : {M : Set c} → Monoid M → (A → M) → T A → M

open Foldable public

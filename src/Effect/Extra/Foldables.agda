{-# OPTIONS --without-K --safe #-}

module Effect.Extra.Foldables where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat.Base hiding (_⊔_)

open import Data.Extra.Nat.Instances
open import Structures.Monoids


private
  variable
    a b c : Level
    A : Set a

record Foldable {c} (T : Set a → Set b) : Set (lsuc a ⊔ b ⊔ lsuc c) where
  field
    foldMap : {M : Set c} → Monoid M → (A → M) → T A → M

open Foldable public

length : ∀ {A} {T : Set a → Set b} → Foldable {c = lzero} T → T A → ℕ
length F = foldMap F ℕ-+-M (λ _ → 1)

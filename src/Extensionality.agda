{-# OPTIONS --cubical-compatible #-}

module Extensionality where

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)


private
  variable
    a b : Level


postulate
  f-ext : ∀ {ℓ ℓ′} {A : Set ℓ} {B : A → Set ℓ′} {f g : (a : A) → B a} → (∀ x → f x ≡ g x) → f ≡ g

f-ext' : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
f-ext' = f-ext

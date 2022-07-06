{-# OPTIONS --without-K #-}

module Extensionality where

open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  f-ext : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

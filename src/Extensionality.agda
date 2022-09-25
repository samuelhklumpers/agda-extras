{-# OPTIONS --without-K #-}

module Extensionality where

open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  f-ext : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
  f-ext' : ∀ {ℓ ℓ′} {A : Set ℓ} {B : A → Set ℓ′} {f g : (a : A) → B a} → (∀ x → f x ≡ g x) → f ≡ g

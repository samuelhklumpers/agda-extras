{-# OPTIONS --without-K --safe #-}

module Structures.Monoids where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Structures.Semigroups public

private
  variable
    a b : Level

record RawMonoid (M : Set a) : Set a where
  field
    rawMS : RawSemigroup M
    mempty : M

record Monoid (M : Set a) : Set a where
  field
    rawM : RawMonoid M
    semi : Semigroup M

  private
    open module Y = RawMonoid rawM
    open module X = RawSemigroup rawMS

  field
    left-id  : (x : M) → mempty <> x ≡ x
    right-id : (x : M) → x <> mempty ≡ x

open Monoid public

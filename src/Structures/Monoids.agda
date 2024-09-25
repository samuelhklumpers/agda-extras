{-# OPTIONS --cubical-compatible --safe #-}

module Structures.Monoids where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Structures.Semigroups public

private
  variable
    a b : Level

record RawMonoid (M : Set a) : Set a where
  field
    rawS : RawSemigroup M
    mempty : M

open RawMonoid public

instance
  Refl : {A : Set a} {x : A} → x ≡ x
  Refl = refl

record Monoid (M : Set a) : Set a where
  field
    rawM : RawMonoid M
    semi : Semigroup M
    {{consistent}} : rawM .rawS ≡ semi .rawS

  private
    open module Y = RawMonoid rawM renaming (mempty to memptyM)
    open module X = RawSemigroup (semi .rawS) renaming (_<>_ to _<>M_)

  field
    left-id  : (x : M) → memptyM <>M x ≡ x
    right-id : (x : M) → x <>M memptyM ≡ x

open Monoid public

record MonoidHom {M₀ : Set a} {N₀ : Set b} (M : Monoid M₀) (N : Monoid N₀) (morph : M₀ → N₀) : Set (a ⊔ b) where
  field
    m-neutral : morph (M .rawM .mempty) ≡ N .rawM .mempty
    m-mappend : (x y : M₀) → morph (mappend (M .semi .rawS) x y) ≡ mappend (N .semi .rawS) (morph x) (morph y)

open MonoidHom public

{-# OPTIONS --without-K --safe #-}

module Structures.Semigroups where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    a : Level

record RawSemigroup (G : Set a) : Set a where
  infixr 6 _<>_
  
  field
    _<>_ : G → G → G

mappend : {G : Set a} → RawSemigroup G → G → G → G
mappend G = G .RawSemigroup._<>_

record Semigroup (G : Set a) : Set a where
  field
    rawS : RawSemigroup G

  private
    open module X = RawSemigroup rawS

  field
    assoc : (x y z : G) → x <> y <> z ≡ (x <> y) <> z

open Semigroup public

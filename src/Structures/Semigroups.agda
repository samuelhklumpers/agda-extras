{-# OPTIONS --cubical-compatible --safe #-}

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

open RawSemigroup public

mappend : {G : Set a} → RawSemigroup G → G → G → G
mappend G = G .RawSemigroup._<>_

record Semigroup (G : Set a) : Set a where
  field
    rawS : RawSemigroup G

  private
    open module X = RawSemigroup rawS renaming (_<>_ to _<>S_)

  field
    assoc : (x y z : G) → (x <>S y) <>S z ≡ x <>S (y <>S z)

open Semigroup public

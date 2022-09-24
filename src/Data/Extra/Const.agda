{-# OPTIONS --without-K --safe #-}

module Data.Extra.Const where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)


private
  variable
    a b : Level


record Const (A : Set a) (B : Set b) : Set a where
  constructor mkConst
  field
    runConst : A

open Const public

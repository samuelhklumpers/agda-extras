{-# OPTIONS --without-K --safe #-}

module Data.Extra.Const where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Monoids
open import Applicatives


private
  variable
    a b : Level

record Const (A : Set a) (B : Set b) : Set a where
  constructor mkConst
  field
    runConst : A

open Const public

open Monoid

ConstRawA : {M : Set a} → RawMonoid M → RawApplicative {a = b} (Const M)
ConstRawA mon = record {
  pure = λ _ → mkConst mempty ;
  ap = λ { (mkConst x) (mkConst y) → mkConst (x <> y) } }
    where
      open RawMonoid mon
      open RawSemigroup rawMS

{-# OPTIONS --without-K --safe #-}

module Data.Extra.Const.Instances where

open import Level

open import Data.Extra.Const
open import Effect.Extra.Applicatives
open import Structures.Monoids


private
  variable
    a b : Level


open Monoid

ConstRawA : {M : Set a} → RawMonoid M → RawApplicative {a = b} (Const M)
ConstRawA mon = record {
  pure = λ _ → mkConst memptyM ;
  ap = λ { (mkConst x) (mkConst y) → mkConst (x <>M y) } }
    where
      open RawMonoid mon renaming (mempty to memptyM)
      open RawSemigroup (mon .rawS) renaming (_<>_ to _<>M_)

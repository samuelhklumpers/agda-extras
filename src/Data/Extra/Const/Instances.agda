{-# OPTIONS --without-K --safe #-}

module Data.Extra.Const.Instances where

open import Prelude

open import Data.Extra.Const
open import Effect.Extra.Applicatives
open import Structures.Monoids


private
  variable
    a b : Level
    A : Set a

open Monoid

ConstRawA : {M : Set a} → RawMonoid M → RawApplicative {a = b} (Const M)
ConstRawA mon = record {
  pure = λ _ → mkConst memptyM ;
  ap = λ { (mkConst x) (mkConst y) → mkConst (x <>M y) } }
    where
      open RawMonoid mon renaming (mempty to memptyM)
      open RawSemigroup (mon .rawS) renaming (_<>_ to _<>M_)

constRawA : Monoid A → RawApplicative {a = a} {b = b} (const A)
constRawA M = record { pure = const memptyM ; ap = _<>M_ }
  where
    open RawMonoid (M .rawM) renaming (mempty to memptyM)
    open RawSemigroup (M .semi .rawS) renaming (_<>_ to _<>M_)

constA : ∀ {A} → Monoid A → Applicative {a = a} {b = b} (const A)
constA M = record
  { rawIA = constRawA M
  ; a-ident = left-id M
  ; a-comp = λ u v w → trans (cong (λ k → (k <>M v) <>M w) (left-id M u)) (assoc (M .semi) u v w)
  ; hom = λ _ _ → left-id M memptyM
  ; inter = λ u _ → trans (right-id M u) (sym (left-id M u)) }
  where
    open module X = RawMonoid (M .rawM) renaming (mempty to memptyM)
    open module Y = RawSemigroup (M .semi .rawS) renaming (_<>_ to _<>M_)

{-# OPTIONS --safe --without-K #-}

module Data.Extra.Nat.Instances where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

open import Structures.Semigroups
open import Structures.Monoids


ℕ-+-RawS : RawSemigroup ℕ
ℕ-+-RawS = record { _<>_ = _+_ }

ℕ-+-S : Semigroup ℕ
ℕ-+-S = record { rawS = ℕ-+-RawS ; assoc = +-assoc }

ℕ-+-RawM : RawMonoid ℕ
ℕ-+-RawM = record { rawS = ℕ-+-RawS ; mempty = 0 }

ℕ-+-M : Monoid ℕ
ℕ-+-M = record { rawM = ℕ-+-RawM ; semi = ℕ-+-S ; left-id = λ _ → refl ; right-id = +-identityʳ }

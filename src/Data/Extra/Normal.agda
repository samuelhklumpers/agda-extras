module Data.Extra.Normal where

open import Level
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base

private
  variable
    a b : Level


-- see: https://stackoverflow.com/a/32821966/5895919
data Normal (Shape : ℕ → Set a) (A : Set b) : Set (a ⊔ b) where
  _:-_ : ∀ {n} → Shape n → Vec A n → Normal Shape A


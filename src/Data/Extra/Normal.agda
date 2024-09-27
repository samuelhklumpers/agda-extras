{-# OPTIONS --cubical-compatible #-}

module Data.Extra.Normal where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ; Σ-syntax)
open import Data.Vec.Base using (Vec)

private
  variable
    a b : Level

infix 5 _▷_
record FinContainer (s : Level) : Set (lsuc s) where
  constructor _▷_
  field
    Shape : Set s
    size  : Shape → ℕ
open FinContainer public

data Normal (C : FinContainer a) (A : Set b) : Set (a ⊔ b) where
  _:-_ : (s : Shape C) → Vec A (size C s) → Normal C A

--⟦_⟧ : FinContainer a → Set b → Set (a ⊔ b)
--⟦ S ▷ sz ⟧ X = Σ[ s ∈ S ] Vec X (sz s)

{-
-- see: https://stackoverflow.com/a/32821966/5895919
data Normal (Shape : ℕ → Set a) (A : Set b) : Set (a ⊔ b) where
  _:-_ : ∀ {n} → Shape n → Vec A n → Normal Shape A
-}

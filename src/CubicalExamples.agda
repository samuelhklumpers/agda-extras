{-# OPTIONS --guardedness --cubical #-}

module CubicalExamples where

open import Cubical.Core.Everything hiding (_≡_)

open import Level
open import Data.Nat renaming (suc to succ)
open import Relation.Binary.PropositionalEquality

open import Extensionality
open import Representables


private
  variable
    ℓ : Level
    A : Set ℓ


module StreamEx where
  record Stream {ℓ} (A : Set ℓ) : Set ℓ where
    constructor _⇉_
    coinductive
    field
      hd : A
      tl : Stream A

  open Stream

  ix : Stream A → ℕ → A
  ix s 0        = hd s
  ix s (succ i) = ix (tl s) i

  gen : (ℕ → A) → Stream A
  hd (gen f) = f 0
  tl (gen f) = gen (λ i → f (succ i))

  -- Streams aren't that representable without cubical...

  instance
    StreamRep : ∀ {ℓ} → Representable {ℓ = ℓ} Stream
    StreamRep = record {
      Rep = ℕ ;
      iso = λ A → record {
        to = ix ;
        from = gen ;
        retract = λ x → {!!} ;
        section = λ f → f-ext λ i → section' f i } }
          where
            section' : (f : ℕ → A) (j : ℕ) → ix (gen f) j ≡ f j
            section' f 0        = refl
            section' f (succ j) = section' (λ i → f (succ i)) j

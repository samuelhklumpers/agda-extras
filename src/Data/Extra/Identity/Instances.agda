{-# OPTIONS --without-K #-}

module Data.Extra.Identity.Instances where

open import Function.Base using (id; _∘′_)
open import Level
open import Relation.Binary.PropositionalEquality
open import Effect.Functor

open import Data.Extra.Identity
open import Effect.Extra.Functors
open import Effect.Extra.Applicatives
open import Effect.Extra.Monads

open ≡-Reasoning

private
  variable
    a b c : Level



IdRawA : ∀ {a} → RawApplicative {a = a} Identity
IdRawA = record {
  pure = identity ;
  ap = λ { (identity f) (identity x) → identity (f x) }
  }

IdA : ∀ {a} → Applicative {a = a} Identity
IdA = record {
  rawIA = IdRawA ;
  a-ident = λ { (identity x) → refl } ;
  a-comp = λ { (identity u) (identity v) (identity w) → refl } ;
  hom = λ f x → refl ;
  inter = λ { (identity u) y → refl } }




IdRawM : RawMonad {a = a} Identity
IdRawM = record { return = identity ; _>>=_ = λ x f → f (runIdentity x) }

IdM : Monad {a = a} Identity
IdM = record {
  rawM = IdRawM ;
  left-id = λ _ _ → refl ;
  right-id = λ { (identity x) → refl } ;
  assoc = λ _ _ _ → refl }

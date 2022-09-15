{-# OPTIONS --without-K #-}

module Data.Extra.Identity where

open import Function.Base using (id; _∘′_)
open import Level
open import Relation.Binary.PropositionalEquality
open import Effect.Functor
open import Effect.Monad

open import Functors
open import Applicatives
open import Extensionality

open ≡-Reasoning

private
  variable
    a b c : Level


record Identity (A : Set a) : Set a where
  constructor identity
  field
    runIdentity : A
    
open Identity public


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

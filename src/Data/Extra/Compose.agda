{-# OPTIONS --without-K #-}

module Data.Extra.Compose where

open import Function.Base using (id; _∘′_)
open import Level
open import Relation.Binary.PropositionalEquality
open import Effect.Functor
open import Effect.Monad

open import Effect.Extra.Functors
open import Effect.Extra.Applicatives
open import Extensionality

open ≡-Reasoning

private
  variable
    a b c : Level


record Compose (G : Set b → Set c) (F : Set a → Set b) (A : Set a) : Set (a ⊔ b ⊔ c) where
  constructor compose
  field
    runCompose : G (F A)
    
open Compose public



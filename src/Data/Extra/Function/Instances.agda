{-# OPTIONS --without-K #-}

module Data.Extra.Function.Instances where

open import Relation.Binary.PropositionalEquality
open import Level

open import Effect.Extra.Monads
open import Extensionality


private
  variable
    a b c : Level
    A : Set a
    B : Set b


FunctionRawM : RawMonad {a = a} (λ B → (A → B))
FunctionRawM = record { return = λ x _ → x ; _>>=_ = λ f g x → g (f x) x }

FunctionM : Monad {a = a} (λ B → (A → B))
FunctionM = record {
  rawM = FunctionRawM ;
  left-id = λ a f → f-ext (λ x → refl) ;
  right-id = λ m → f-ext (λ x → refl) ;
  assoc = λ m f g → f-ext (λ x → refl) }


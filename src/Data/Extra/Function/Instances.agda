{-# OPTIONS --without-K #-}

module Data.Extra.Function.Instances where

open import Effect.Functor
open import Function.Base using (_∘′_; const)
open import Level
open import Relation.Binary.PropositionalEquality

open import Effect.Extra.Functors
open import Effect.Extra.Applicatives
open import Effect.Extra.Monads
open import Extensionality


private
  variable
    a b c : Level
    A : Set a
    B : Set b


FunctionRawF : RawFunctor {ℓ = a} (λ B → (A → B))
FunctionRawF = record
  { _<$>_ = _∘′_
  }

FunctionF : Functor {a = a} (λ B → (A → B))
FunctionF = record
  { rawF = FunctionRawF
  ; f-ident = λ x → refl
  ; f-comp = λ g f x → refl
  }

FunctionRawA : RawApplicative {a = a} (λ B → (A → B))
FunctionRawA = record
  { pure = const
  ; ap = λ g f x → g x (f x) }

FunctionA : Applicative {a = a} (λ B → (A → B))
FunctionA = record
  { rawIA = FunctionRawA
  ; a-ident = λ v → refl
  ; a-comp = λ u v w → refl
  ; hom = λ f x → refl ;
  inter = λ u y → refl } 

FunctionRawM : RawMonad {a = a} (λ B → (A → B))
FunctionRawM = record { return = λ x _ → x ; _>>=_ = λ f g x → g (f x) x }

FunctionM : Monad {a = a} (λ B → (A → B))
FunctionM = record
  { rawM = FunctionRawM
  ; left-id = λ a f → f-ext (λ x → refl)
  ; right-id = λ m → f-ext (λ x → refl)
  ; assoc = λ m f g → f-ext (λ x → refl) }


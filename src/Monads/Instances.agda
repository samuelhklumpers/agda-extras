{-# OPTIONS --without-K #-}

module Monads.Instances where

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Level

open import Extensionality
open import Functors
open import Applicatives
open import Monads


private
  variable
    a b : Level
    A : Set a
    B : Set b

-- the function (r →) monad

FunctionF : Set a → Set b → Set (a ⊔ b)
FunctionF a b = a → b

FunctionF' : Set a → ⊤ → ⊤ → Set b → Set (a ⊔ b)
FunctionF' a _ _ = FunctionF a


instance
  FunctionRawM : RawIMonad' {a = a} (FunctionF' A)
  FunctionRawM = record { return = λ x _ → x ; _>>=_ = λ f g x → g (f x) x }

  FunctionPreMon : PreIMonad {a = a} (FunctionF' A)
  FunctionPreMon = record { left-id = λ a f → f-ext (λ x → refl) ; right-id = λ m → f-ext (λ x → refl) ; assoc = λ m f g → f-ext (λ x → refl) }

open module MTA {a} {A : Set a} = MonToApp {a = a} (FunctionF' A)
open module ATF {a} {A : Set a} = AppToFun {a = a} (FunctionF' A)

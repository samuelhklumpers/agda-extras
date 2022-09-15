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
    a b c : Level
    A : Set a
    B : Set b

-- the function (r →) monad

FunctionRawM : RawIMonad {a = a} {I = ⊤} (λ _ _ B → (A → B))
FunctionRawM = record { return = λ x _ → x ; _>>=_ = λ f g x → g (f x) x }

FunctionM : Monad {a = a} (λ B → (A → B))
FunctionM = record {
  rawM = FunctionRawM ;
  left-id = λ a f → f-ext (λ x → refl) ;
  right-id = λ m → f-ext (λ x → refl) ;
  assoc = λ m f g → f-ext (λ x → refl) }

--FunctionA {a} {A : Set a} = MonToApp {a = a} (FunctionF' A) public
--FunctionF {a} {A : Set a} = AppToFun {a = a} (FunctionF' A) public



-- the identity monad


record Identity (A : Set a) : Set a where
  constructor identity
  field
    runIdentity : A

open Identity public

IdRawM : RawMonad {a = a} Identity
IdRawM = record { return = identity ; _>>=_ = λ x f → f (runIdentity x) }

IdM : Monad {a = a} Identity
IdM = record {
  rawM = IdRawM ;
  left-id = λ _ _ → refl ;
  right-id = λ { (identity x) → refl } ;
  assoc = λ _ _ _ → refl }

--open module IdMTA {a} = MonToApp {a = a} {I = ⊤} (λ _ _ → Identity) public renaming (preMonToMon to idMon; monToApp to idPreApp)
--open module IdATF {a} = AppToFun {a = a} {I = ⊤} (λ _ _ → Identity) public renaming (preAppToApp to idApp; preAppToFun to idFun)

{-# OPTIONS --without-K #-}

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.List.Base
open import Data.Vec.Base
open import Data.Nat.Base

module Currying where

data HList {a} : List (Set a) → Set (lsuc a) where
  []ₕ  : HList []
  _∷ₕ_ : ∀ {x xs} → (a : x) → HList xs → HList (x ∷ xs)

Fun : ∀ {a} → List (Set a) → Set a → Set a
Fun []       y = y
Fun (x ∷ xs) y = x → Fun xs y

FunN : ∀ {a n} → Vec (Set a) n → Set a → Set a
FunN []       y = y
FunN (x ∷ xs) y = x → FunN xs y

UFun : ∀ {a} → List (Set a) → Set a → Set (lsuc a)
UFun xs x = HList xs → x

uncurry : ∀ {a xs} {x : Set a} → Fun xs x → HList xs → x
uncurry f []ₕ = f
uncurry f (x ∷ₕ xs) = uncurry (f x) xs

--uncurryN : ∀ {a n} {xs : Vec (Set a) n} {y : Set a} → FunN xs x → HList 

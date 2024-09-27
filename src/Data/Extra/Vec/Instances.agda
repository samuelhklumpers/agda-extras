{-# OPTIONS --cubical-compatible #-}

module Data.Extra.Vec.Instances where

open import Data.Vec.Base using (Vec; []; _∷_)

open import Effect.Extra.Functors using (fmap)
open import Effect.Extra.Applicatives using (pure; ap; rawATF)
open import Effect.Extra.Traversables using (RawTraversable; traverse)

VecRawTr : ∀ {a b n} → RawTraversable {a} {b} (λ A → Vec A n) 
traverse VecRawTr A f []       = pure A []
traverse VecRawTr A f (x ∷ xs) = ap A (fmap (rawATF A) _∷_ (f x)) (traverse VecRawTr A f xs)

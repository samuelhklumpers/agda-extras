module Functors where

open import Function.Base using (id; _∘′_)
open import Effect.Functor using (RawFunctor)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)


private
  variable
    ℓ ℓ′ : Level
    A B C : Set ℓ

record Functor (F : Set ℓ → Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  field 
    {{Func}} : RawFunctor F
    
  open RawFunctor Func public

  field
    f-ident : (x : F A) → (id <$> x) ≡ x
    f-comp  : (g : B → C) (f : A → B) (x : F A)
          → (g <$> (f <$> x)) ≡ (g ∘′ f <$> x)

open Functor {{...}} public



module Functors where

open import Function.Base using (id; _∘′_)
open import Effect.Functor using (RawFunctor)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)


private
  variable
    ℓ ℓ′ i : Level
    A B C : Set ℓ

record IFunctor {I : Set i} (F : I → Set ℓ → Set ℓ′) : Set (i ⊔ suc ℓ ⊔ ℓ′) where
  field 
    {{Func}} : ∀ {i} → RawFunctor (F i)
    
  open module RF {i : I} = RawFunctor (Func {i = i}) public

  field
    ident : ∀ {i} → (x : F i A) → (id <$> x) ≡ x
    comp  : ∀ {i} → (g : B → C) (f : A → B) (x : F i A)
          → (g <$> (f <$> x)) ≡ (g ∘′ f <$> x)

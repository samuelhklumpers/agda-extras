module Lawful where

open import Function.Base
open import Effect.Functor
open import Effect.Applicative
open import Level
open import Relation.Binary.PropositionalEquality

private
  variable
    ℓ ℓ′ ℓ″ : Level
    A B X Y : Set ℓ


record Functor {F : Set ℓ → Set ℓ′} (Func : RawFunctor F) : Set (suc ℓ ⊔ ℓ′) where
  open RawFunctor Func

  field
    ident : (x : F A) → (id <$> x) ≡ x
    comp  : ∀ {A B C : Set ℓ} (g : B → C) (f : A → B) (x : F A)
          → (g <$> (f <$> x)) ≡ (g ∘ f <$> x)

open ≡-Reasoning


record Applicative {F : Set ℓ → Set ℓ} (App : RawApplicative F) : Set (suc ℓ) where
  open RawApplicative App

  field
    ident : (v : F A)
      → (pure id ⊛ v) ≡ v
      
    comp  : ∀ {A B C} (u : F (B → C)) (v : F (A → B)) (w : F A)
      → (((pure _∘′_ ⊛ u) ⊛ v) ⊛ w) ≡ (u ⊛ (v ⊛ w))
      
    hom   : (f : A → B) (x : A)
      → (pure f ⊛ pure x) ≡ pure (f x)
      
    inter : (u : F (A → B)) (y : A)
      → (u ⊛ pure y) ≡ (pure (_$′ y) ⊛ u)

  functor : Functor rawFunctor
  functor = record {
    ident = ident ;
    comp  = λ g f x → begin
      (pure g ⊛ (pure f ⊛ x))               ≡⟨ sym (comp (pure g) (pure f) x) ⟩
      (((pure _∘′_ ⊛ pure g) ⊛ pure f) ⊛ x) ≡⟨ cong (λ y → (y ⊛ pure f) ⊛ x) (hom _∘′_ g) ⟩
      ((pure (g ∘′_) ⊛ pure f) ⊛ x)         ≡⟨ cong (_⊛ x) (hom (_∘′_ g) f) ⟩  
      (pure (g ∘′ f) ⊛ x) ∎
    }

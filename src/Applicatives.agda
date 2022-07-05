module Applicatives where

open import Function.Base using (id; _$′_; _∘′_)
open import Effect.Functor using (RawFunctor)
open import Effect.Applicative.Indexed using (RawIApplicative; IFun)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Functors


open ≡-Reasoning



private
  variable
    ℓ i : Level
    A B C : Set ℓ


record IApplicative {I : Set i} (F : IFun I ℓ) : Set (i ⊔ suc ℓ) where
  field
    {{App}} : RawIApplicative F
  
  open RawIApplicative App public

  field
    ident : ∀ {i j} → (v : F i j A)
      → (pure id ⊛ v) ≡ v
      
    comp  : ∀ {i j k l} → (u : F i j (B → C)) (v : F j k (A → B)) (w : F k l A)
      → (((pure _∘′_ ⊛ u) ⊛ v) ⊛ w) ≡ (u ⊛ (v ⊛ w))
      
    hom   : ∀ {i} → (f : A → B) (x : A)
      → (pure f ⊛ pure x) ≡ pure {B} {i} (f x)
      
    inter : ∀ {i j} → (u : F i j (A → B)) (y : A)
      → (u ⊛ pure y) ≡ (pure (_$′ y) ⊛ u)

  instance
    AppFunctor : {(i , j) : I × I} → RawFunctor (F i j)
    AppFunctor = rawFunctor

  functor : ∀ {i j} → Functor (F i j)
  functor = record {
    ident = ident ;
    comp  = λ g f x → begin
      (pure g ⊛ (pure f ⊛ x))               ≡⟨ sym (comp (pure g) (pure f) x) ⟩
      (((pure _∘′_ ⊛ pure g) ⊛ pure f) ⊛ x) ≡⟨ cong (λ y → (y ⊛ pure f) ⊛ x) (hom _∘′_ g) ⟩
      ((pure (g ∘′_) ⊛ pure f) ⊛ x)         ≡⟨ cong (_⊛ x) (hom (_∘′_ g) f) ⟩  
      (pure (g ∘′ f) ⊛ x) ∎ }

module Lawful where

open import Function.Base
open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)
open import Level
open import Relation.Binary.PropositionalEquality


private
  variable
    ℓ ℓ′ ℓ″ : Level
    A B X Y : Set ℓ


record Functor (F : Set ℓ → Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  field 
    {{Func}} : RawFunctor F
    
  open RawFunctor Func public

  field
    ident : (x : F A) → (id <$> x) ≡ x
    comp  : ∀ {A B C : Set ℓ} (g : B → C) (f : A → B) (x : F A)
          → (g <$> (f <$> x)) ≡ (g ∘ f <$> x)
  

open ≡-Reasoning


record Applicative (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
  field
    {{App}} : RawApplicative F
  
  open RawApplicative App public

  field
    ident : (v : F A)
      → (pure id ⊛ v) ≡ v
      
    comp  : ∀ {A B C} (u : F (B → C)) (v : F (A → B)) (w : F A)
      → (((pure _∘′_ ⊛ u) ⊛ v) ⊛ w) ≡ (u ⊛ (v ⊛ w))
      
    hom   : (f : A → B) (x : A)
      → (pure f ⊛ pure x) ≡ pure (f x)
      
    inter : (u : F (A → B)) (y : A)
      → (u ⊛ pure y) ≡ (pure (_$′ y) ⊛ u)

  instance
    AppFunctor : RawFunctor F
    AppFunctor = rawFunctor

  functor : Functor F
  functor = record {
    ident = ident ;
    comp  = λ g f x → begin
      (pure g ⊛ (pure f ⊛ x))               ≡⟨ sym (comp (pure g) (pure f) x) ⟩
      (((pure _∘′_ ⊛ pure g) ⊛ pure f) ⊛ x) ≡⟨ cong (λ y → (y ⊛ pure f) ⊛ x) (hom _∘′_ g) ⟩
      ((pure (g ∘′_) ⊛ pure f) ⊛ x)         ≡⟨ cong (_⊛ x) (hom (_∘′_ g) f) ⟩  
      (pure (g ∘′ f) ⊛ x) ∎
    }

  open Functor functor


postulate
  f-ext : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

record Monad (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
  field
    {{Mon}} : RawMonad F

  open RawMonad Mon public

  field
    left-id  : (a : A) (k : A → F B)
      → (return a >>= k) ≡ k a
    right-id : (m : F A)
      → (m >>= return) ≡ m
    assoc    : ∀ {A B C} (m : F A) (k : A → F B) (h : B → F C)
      → (m >>= (λ x → k x >>= h)) ≡ ((m >>= k) >>= h)

  instance
    MonApp : RawApplicative F
    MonApp = rawIApplicative

  applicative : Applicative F
  applicative = record {
      ident = λ v → begin
        (return id >>= (λ f → v >>= λ x → return (f x))) ≡⟨ left-id id ((λ f → v >>= λ x → return (f x))) ⟩
        (v >>= return) ≡⟨ right-id v ⟩
        v ∎ ;
      comp  = λ u v w → begin
        ((((return _∘′_ >>= (λ c → u >>= (λ g → return (c g)))) >>= (λ g' → v >>= (λ f → return (g' f)))) >>= (λ f' → w >>= (λ x → return (f' x)))))
            ≡⟨ cong (λ k → (k >>= (λ g' → v >>= (λ f → return (g' f)))) >>= (λ f' → w >>= (λ x → return (f' x)))) (left-id _∘′_ λ c → u >>= (λ g → return (c g))) ⟩
        (((u >>= (λ g → return (g ∘′_))) >>= (λ g' → v >>= (λ f → return (g' f)))) >>= (λ f' → w >>= (λ x → return (f' x))))
            ≡⟨ cong (λ k → k >>= (λ f' → w >>= (λ x → return (f' x)))) (sym (assoc u (λ g → return (g ∘′_)) λ g' → v >>= (λ f → return (g' f)))) ⟩
        ((u >>= (λ g → return (g ∘′_) >>= (λ g' → v >>= (λ f → return (g' f))))) >>= (λ f' → w >>= (λ x → return (f' x))))
            ≡⟨ cong (λ k → (u >>= k) >>= (λ f' → w >>= (λ x → return (f' x)))) (f-ext (λ g → left-id (g ∘′_) λ g' → v >>= (λ f → return (g' f)))) ⟩
        ((u >>= (λ g → v >>= (λ f → return (g ∘′ f))) >>= (λ f' → w >>= (λ x → return (f' x)))))
            ≡⟨ sym (assoc u (λ g → v >>= (λ f → return (g ∘′ f))) λ f' → w >>= (λ x → return (f' x))) ⟩
        (u >>= (λ g → ((v >>= (λ f → return (g ∘′ f))) >>= (λ f' → w >>= (λ x → return (f' x))))))
            ≡⟨ cong (λ k → u >>= k) (f-ext (λ g → sym (assoc v (λ f → return (g ∘′ f)) λ f' → w >>= (λ x → return (f' x))))) ⟩
        (u >>= (λ g → (v >>= (λ f → return (g ∘′ f) >>= (λ f' → w >>= (λ x → return (f' x)))))))
            ≡⟨ cong (λ k → u >>= k) (f-ext (λ g → cong (λ k' → v >>= k') (f-ext (λ f → left-id (g ∘′ f) (λ f' → w >>= (λ x → return (f' x))))))) ⟩
        (u >>= (λ g → (v >>= (λ f → (w >>= (λ x → return (g (f x))))))))
            ≡⟨ cong (λ k → u >>= k) (f-ext (λ g → cong (λ k' → v >>= k') (f-ext λ f → cong (λ k'' → w >>= k'') (f-ext (λ x → sym (left-id (f x) λ y → return (g y))))))) ⟩
        (u >>= (λ g → (v >>= (λ f → (w >>= (λ x → return (f x) >>= (λ y → return (g y))))))))
            ≡⟨ cong (λ k → u >>= k) (f-ext (λ g → cong (λ k' → v >>= k') (f-ext λ f → assoc w (λ x → return (f x)) (λ y → return (g y))))) ⟩
        (u >>= (λ g → (v >>= (λ f → (w >>= (λ x → return (f x))) >>= (λ y → return (g y))))))
            ≡⟨ cong (λ k → u >>= k) (f-ext (λ g → assoc v (λ f → w >>= (λ x → return (f x))) λ y → return (g y))) ⟩
        (u >>= (λ g → (v >>= (λ f → w >>= (λ x → return (f x)))) >>= (λ y → return (g y)))) ∎ ;
      hom   = λ f x → begin
        (return f >>= (λ f' → return x >>= (λ x' → return (f' x')))) ≡⟨ left-id f (λ f' → return x >>= (λ x' → return (f' x'))) ⟩
        (return x >>= (λ x' → return (f x'))) ≡⟨ left-id x (λ x' → return (f x')) ⟩
        return (f x) ∎ ;
      inter = λ u y → begin
        (u >>= (λ f → return y >>= λ x → return (f x))) ≡⟨ cong (λ z → u >>= z) (f-ext (λ f → left-id y λ x → return (f x))) ⟩
        (u >>= (λ f → return (f y))) ≡⟨ sym (left-id (_$′ y) λ x → u >>= (λ f → return (x f))) ⟩
        (return (_$′ y) >>= (λ x → u >>= (λ f → return (x f)))) ∎
    }

  open Applicative applicative

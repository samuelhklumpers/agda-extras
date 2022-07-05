module Monads where

open import Function.Base using (id; _$′_; _∘′_)
open import Effect.Functor using (RawFunctor)
open import Effect.Applicative.Indexed using (RawIApplicative; IFun)
open import Effect.Monad.Indexed using (RawIMonad)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality

open import Extensionality
open import Functors
open import Applicatives

private
  variable
    ℓ i : Level
    A B C : Set ℓ

open ≡-Reasoning


record IMonad {I : Set i} (F : IFun I ℓ) : Set (i ⊔ suc ℓ) where
  field
    {{Mon}} : RawIMonad F

  open RawIMonad Mon public

  field
    left-id  : ∀ {i j} → (a : A) (f : A → F i j B)
      → (return a >>= f) ≡ f a
    right-id : ∀ {i j} → (m : F i j A)
      → (m >>= return) ≡ m
    assoc    : ∀ {i j k l} → (m : F i j A) (f : A → F j k B) (g : B → F k l C)
      → (m >>= (λ x → f x >>= g)) ≡ ((m >>= f) >>= g)

  instance
    MonApp : RawIApplicative F
    MonApp = rawIApplicative

  applicative : IApplicative F
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

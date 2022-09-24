{-# OPTIONS --without-K #-}

module Effect.Extra.Monads where

open import Function.Base using (id; _$′_; _∘′_)
open import Effect.Functor using (RawFunctor)
open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Unit

open import Extensionality
open import Effect.Extra.Applicatives


private
  variable
    p a b : Level
    A B C : Set a


record RawIMonad {I : Set p} (M : HIFun I a b) : Set (p ⊔ suc a ⊔ b) where
  infixl 1 _>>=_ _>>_

  field
    return : ∀ {i} → A → M i i A
    _>>=_  : ∀ {i j k} → M i j A → (A → M j k B) → M i k B

  _>>_ : ∀ {i j k} → M i j A → M j k B → M i k B
  m₁ >> m₂ = m₁ >>= λ _ → m₂


bind : {I : Set p} {i j k : I} {M : HIFun I a b} → RawIMonad M → M i j A → (A → M j k B) → M i k B
bind M = M .RawIMonad._>>=_

RawMonad : (Set a → Set b) → Set (suc a ⊔ b)
RawMonad M = RawIMonad {I = ⊤} (λ _ _ → M)

record IMonad {I : Set p} (F : HIFun I a b) : Set (p ⊔ suc a ⊔ b) where
  field
    rawM : RawIMonad F

  private
    open module X = RawIMonad rawM

  field
    left-id  : ∀ {i j} {A : Set a} → (a : A) (f : A → F i j B)
      → (return a >>= f) ≡ f a
    right-id : ∀ {i j} → (m : F i j A)
      → (m >>= return) ≡ m
    assoc    : ∀ {i j k l} → (m : F i j A) (f : A → F j k B) (g : B → F k l C)
      → (m >>= (λ x → f x >>= g)) ≡ ((m >>= f) >>= g)


open IMonad public

Monad : (Set a → Set b) → Set (suc a ⊔ b)
Monad F = IMonad {I = ⊤} (λ _ _ → F)


open ≡-Reasoning

module MonToApp {i a b} {I : Set i} (F : HIFun I a b) where
  monToApp : IMonad F → IApplicative F
  monToApp M = record {
      rawIA = record { pure = return ; ap = λ f x → f >>= λ f′ → x >>= λ x′ → return (f′ x′) } ;
      a-ident = λ v → begin
        (return id >>= (λ f → v >>= λ x → return (f x))) ≡⟨ left-id M id ((λ f → v >>= λ x → return (f x))) ⟩
        (v >>= return) ≡⟨ right-id M v ⟩
        v ∎ ;
      -- TODO Cong-Reasoning
      a-comp  = λ u v w → begin
        ((((return _∘′_ >>= (λ c → u >>= (λ g → return (c g)))) >>= (λ g' → v >>= (λ f → return (g' f)))) >>= (λ f' → w >>= (λ x → return (f' x)))))
            ≡⟨ cong (λ k → (k >>= (λ g' → v >>= (λ f → return (g' f)))) >>= (λ f' → w >>= (λ x → return (f' x)))) (left-id M _∘′_ λ c → u >>= (λ g → return (c g))) ⟩
        (((u >>= (λ g → return (g ∘′_))) >>= (λ g' → v >>= (λ f → return (g' f)))) >>= (λ f' → w >>= (λ x → return (f' x))))
            ≡⟨ cong (λ k → k >>= (λ f' → w >>= (λ x → return (f' x)))) (sym (assoc M u (λ g → return (g ∘′_)) λ g' → v >>= (λ f → return (g' f)))) ⟩
        ((u >>= (λ g → return (g ∘′_) >>= (λ g' → v >>= (λ f → return (g' f))))) >>= (λ f' → w >>= (λ x → return (f' x))))
            ≡⟨ cong (λ k → (u >>= k) >>= (λ f' → w >>= (λ x → return (f' x)))) (f-ext (λ g → left-id M (g ∘′_) λ g' → v >>= (λ f → return (g' f)))) ⟩
        ((u >>= (λ g → v >>= (λ f → return (g ∘′ f))) >>= (λ f' → w >>= (λ x → return (f' x)))))
            ≡⟨ sym (assoc M u (λ g → v >>= (λ f → return (g ∘′ f))) λ f' → w >>= (λ x → return (f' x))) ⟩
        (u >>= (λ g → ((v >>= (λ f → return (g ∘′ f))) >>= (λ f' → w >>= (λ x → return (f' x))))))
            ≡⟨ cong (λ k → u >>= k) (f-ext (λ g → sym (assoc M v (λ f → return (g ∘′ f)) λ f' → w >>= (λ x → return (f' x))))) ⟩
        (u >>= (λ g → (v >>= (λ f → return (g ∘′ f) >>= (λ f' → w >>= (λ x → return (f' x)))))))
            ≡⟨ cong (λ k → u >>= k) (f-ext (λ g → cong (λ k' → v >>= k') (f-ext (λ f → left-id M (g ∘′ f) (λ f' → w >>= (λ x → return (f' x))))))) ⟩
        (u >>= (λ g → (v >>= (λ f → (w >>= (λ x → return (g (f x))))))))
            ≡⟨ cong (λ k → u >>= k) (f-ext (λ g → cong (λ k' → v >>= k') (f-ext λ f → cong (λ k'' → w >>= k'') (f-ext (λ x → sym (left-id M (f x) λ y → return (g y))))))) ⟩
        (u >>= (λ g → (v >>= (λ f → (w >>= (λ x → return (f x) >>= (λ y → return (g y))))))))
            ≡⟨ cong (λ k → u >>= k) (f-ext (λ g → cong (λ k' → v >>= k') (f-ext λ f → assoc M w (λ x → return (f x)) (λ y → return (g y))))) ⟩
        (u >>= (λ g → (v >>= (λ f → (w >>= (λ x → return (f x))) >>= (λ y → return (g y))))))
            ≡⟨ cong (λ k → u >>= k) (f-ext (λ g → assoc M v (λ f → w >>= (λ x → return (f x))) λ y → return (g y))) ⟩
        (u >>= (λ g → (v >>= (λ f → w >>= (λ x → return (f x)))) >>= (λ y → return (g y)))) ∎ ;
      hom   = λ f x → begin
        (return f >>= (λ f' → return x >>= (λ x' → return (f' x')))) ≡⟨ left-id M f (λ f' → return x >>= (λ x' → return (f' x'))) ⟩
        (return x >>= (λ x' → return (f x'))) ≡⟨ left-id M x (λ x' → return (f x')) ⟩
        return (f x) ∎ ;
      inter = λ u y → begin
        (u >>= (λ f → return y >>= λ x → return (f x))) ≡⟨ cong (λ z → u >>= z) (f-ext (λ f → left-id M y λ x → return (f x))) ⟩
        (u >>= (λ f → return (f y))) ≡⟨ sym (left-id M (_$′ y) λ x → u >>= (λ f → return (x f))) ⟩
        (return (_$′ y) >>= (λ x → u >>= (λ f → return (x f)))) ∎
    }
        where
          open RawIMonad (M .rawM)

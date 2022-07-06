module Representables where

open import Level
open import Relation.Binary.PropositionalEquality
open import Effect.Monad.Indexed
open import Function
open import Data.Unit

open import Extensionality
open import Monads public

open ≡-Reasoning


private
  variable
    ℓ ℓ′ : Level
    A B C : Set ℓ


record _≅_ (A : Set ℓ) (B : Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  field
    to   : A → B
    from : B → A
    retract : (x : A) → from (to x) ≡ x
    section : (y : B) → to (from y) ≡ y


record Representable (F : Set ℓ → Set ℓ) : Set (suc ℓ ⊔ suc ℓ′) where
  field
    Rep : Set ℓ′
    iso : (A : Set ℓ) → F A ≅ (Rep → A)

  index : F A → Rep → A
  index {A} = _≅_.to (iso A)
  tabulate : (Rep → A) → F A
  tabulate {A} = _≅_.from (iso A)

  instance
    RepMon : RawIMonad {I = ⊤} (λ _ _ → F)
    RepMon = record {
      return = λ x   → tabulate (const x) ;
      _>>=_  = λ m f → tabulate (λ a → index (f (index m a)) a) }

  repRetract : (k : F A) → tabulate (index k) ≡ k
  repRetract {A} = _≅_.retract (iso A)
  repSection : (f : Rep → A) → index (tabulate f) ≡ f
  repSection {A} = _≅_.section (iso A)

  left-lem : (a : A) (k : A → F B) → (λ b → index (k (index (tabulate (const a)) b)) b) ≡ index (k a)
  left-lem a k = f-ext λ i → begin
    index (k (index (tabulate (const a)) i)) i ≡⟨ cong (λ z → index (k (z i)) i) (repSection (const a)) ⟩
    index (k a) i ∎

  right-lem : (m : F A) → (λ a → index (tabulate (const (index m a))) a) ≡ index m
  right-lem m = f-ext λ i → begin
    index (tabulate (const (index m i))) i ≡⟨ cong (λ z → z i) (repSection (const (index m i))) ⟩
    index m i ∎

  assoc-lem : (m : F A) (k : A → F B) (h : B → F C) (a : Rep) → index (tabulate (λ b → index (h (index (k (index m a)) b)) b)) a ≡ index (h (index (tabulate (λ b → index (k (index m b)) b)) a)) a
  assoc-lem m k h a = begin
    index (tabulate (λ b → index (h (index (k (index m a)) b)) b)) a ≡⟨ cong (λ z → z a) (repSection (λ b → index (h (index (k (index m a)) b)) b)) ⟩
    index (h (index (k (index m a)) a)) a ≡⟨ cong (λ z → index (h (z a)) a) (sym (repSection (λ b → index (k (index m b)) b))) ⟩
    index (h (index (tabulate (λ b → index (k (index m b)) b)) a)) a ∎
  
open Representable {{...}} public

instance
  monad : {F : Set ℓ → Set ℓ} → {{Representable {ℓ′ = ℓ′} F}} → IMonad {I = ⊤} (λ _ _ → F)
  monad = record {
    left-id = λ a k → begin
      tabulate (λ j → index (k (index (tabulate (const a)) j)) j) ≡⟨ cong tabulate (left-lem a k) ⟩
      tabulate (index (k a)) ≡⟨ repRetract (k a) ⟩
      k a ∎ ;
    right-id = λ m → begin
      tabulate (λ a → index (tabulate (const (index m a))) a) ≡⟨ cong tabulate (right-lem m) ⟩
      tabulate (index m) ≡⟨ repRetract m ⟩
      m ∎ ;
    assoc = λ m k h → cong tabulate (f-ext (λ i → assoc-lem m k h i)) }

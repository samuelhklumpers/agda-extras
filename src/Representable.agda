module Representable2 where

open import Level
open import Relation.Binary.PropositionalEquality
open import Effect.Monad
open import Function

open import Lawful

private
  variable
    ℓ ℓ′ ℓ″ : Level


record _≅_ {ℓ} (A B : Set ℓ) : Set ℓ where
  field
    to   : A → B
    from : B → A
    retract : (x : A) → from (to x) ≡ x
    section : (y : B) → to (from y) ≡ y


{-
-- remark: functors that go down the Set hierarchy are _never_ representable: the level of F A would be lower than that of Rep → A 
record Representable' (F : Set ℓ → Set (ℓ ⊔ ℓ′)) : Set (suc ℓ ⊔ suc ℓ′) where
  field
    Rep : Set ℓ′
    iso : (A : Set ℓ) → F A ≅ (Rep → A)
-}


open ≡-Reasoning

record Representable (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
  field
    Rep : Set ℓ
    iso : (A : Set ℓ) → F A ≅ (Rep → A)

  index : {A : Set ℓ} → F A → Rep → A
  index {A} = _≅_.to (iso A)
  tabulate : {A : Set ℓ} → (Rep → A) → F A
  tabulate {A} = _≅_.from (iso A)

  instance
    RepMon : RawMonad F
    RepMon = record {
      return = λ x   → tabulate (const x) ;
      _>>=_  = λ m f → tabulate (λ a → index (f (index m a)) a) }

  private
    retract : {A : Set ℓ} (k : F A) → tabulate (index k) ≡ k
    retract {A} = _≅_.retract (iso A)
    section : {A : Set ℓ} (f : Rep → A) → index (tabulate f) ≡ f
    section {A} = _≅_.section (iso A)

    left-lem : ∀ {A B} (a : A) (k : A → F B) → (λ b → index (k (index (tabulate (const a)) b)) b) ≡ index (k a)
    left-lem a k = f-ext λ i → begin
      index (k (index (tabulate (const a)) i)) i ≡⟨ cong (λ z → index (k (z i)) i) (section (const a)) ⟩
      index (k a) i ∎

    right-lem : ∀ {A} (m : F A) → (λ a → index (tabulate (const (index m a))) a) ≡ index m
    right-lem m = f-ext λ i → begin
      index (tabulate (const (index m i))) i ≡⟨ cong (λ z → z i) (section (const (index m i))) ⟩
      index m i ∎

    assoc-lem : ∀ {A B C}  (m : F A) (k : A → F B) (h : B → F C) (i : Rep) → index (tabulate (λ a → index (h (index (k (index m i)) a)) a)) i ≡ index (h (index (tabulate (λ a → index (k (index m a)) a)) i)) i
    assoc-lem m k h i = begin
      index (tabulate (λ a → index (h (index (k (index m i)) a)) a)) i ≡⟨ cong (λ z → z i) (section (λ a → index (h (index (k (index m i)) a)) a)) ⟩
      index (h (index (k (index m i)) i)) i ≡⟨ cong (λ z → index (h (z i)) i) (sym (section (λ a → index (k (index m a)) a))) ⟩
      index (h (index (tabulate (λ a → index (k (index m a)) a)) i)) i ∎

  monad : Monad F
  monad = record {
    left-id = λ a k → begin
      tabulate (λ j → index (k (index (tabulate (const a)) j)) j) ≡⟨ cong tabulate (left-lem a k) ⟩
      tabulate (index (k a)) ≡⟨ retract (k a) ⟩
      k a ∎ ;
    right-id = λ m → begin
      tabulate (λ a → index (tabulate (const (index m a))) a) ≡⟨ cong tabulate (right-lem m) ⟩
      tabulate (index m) ≡⟨ retract m ⟩
      m ∎ ;
    assoc = λ m k h → cong tabulate (f-ext (λ i → assoc-lem m k h i)) }


    
    

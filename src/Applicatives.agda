{-# OPTIONS --without-K --safe #-}

module Applicatives where

open import Function.Base using (id; _$′_; _∘′_)
open import Effect.Functor using (RawFunctor)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Unit
open import Level renaming (zero to lzero)

open import Functors public

open ≡-Reasoning


private
  variable
    p a b : Level
    A B C : Set a

HIFun : Set p → (a b : Level) → Set (p ⊔ suc a ⊔ suc b)
HIFun I a b = I → I → Set a → Set b


record RawIApplicative {I : Set p} (F : HIFun I a b) : Set (p ⊔ suc a ⊔ b) where
  infixl 4 _⊛_ 
  field
    pure : ∀ {i} → A → F i i A
    _⊛_  : ∀ {i j k} → F i j (A → B) → F j k A → F i k B

--open RawIApplicative public

ap : {A B : Set a} {I : Set p} {i j k : I} {F : HIFun I a b} → RawIApplicative F
   → F i j (A → B) → F j k A → F i k B
ap F = F .RawIApplicative._⊛_

RawApplicative : (Set a → Set b) → Set (suc a ⊔ b)
RawApplicative F = RawIApplicative {I = ⊤} (λ _ _ → F)


record IApplicative {I : Set p} (F : HIFun I a b) : Set (p ⊔ suc a ⊔ b) where
  field
    rawIA : RawIApplicative F

  private
    open module X = RawIApplicative rawIA

  field
    a-ident : ∀ {i j} → (v : F i j A)
      → ((pure id) ⊛ v) ≡ v
      
    a-comp  : ∀ {i j k l} → (u : F i j (B → C)) (v : F j k (A → B)) (w : F k l A)
      → (((pure _∘′_ ⊛ u) ⊛ v) ⊛ w) ≡ (u ⊛ (v ⊛ w))
      
    hom   : ∀ {i} → (f : A → B) (x : A)
      → (pure {i = i} f ⊛ pure x) ≡ pure (f x)
      
    inter : ∀ {i j} → (u : F i j (A → B)) (y : A)
      → (u ⊛ pure y) ≡ (pure (_$′ y) ⊛ u)


open IApplicative public

Applicative : (Set a → Set b) → Set (suc a ⊔ b)
Applicative F = IApplicative {I = ⊤} (λ _ _ → F)


module AppToFun {p a b} {I : Set p} (F : HIFun I a b) where
  preAppToFun : IApplicative F → {k l : I} → Functor (F k l)
  preAppToFun A {k = k} {l = l} = record {
    rawF = record { _<$>_ = λ f x → pure f ⊛ x } ;
    f-ident = a-ident A ;
    f-comp =  λ g f x → begin
      (pure g ⊛ (pure f ⊛ x))               ≡⟨ sym (a-comp A (pure g) (pure f) x) ⟩
      (((pure _∘′_ ⊛ pure g) ⊛ pure f) ⊛ x) ≡⟨ cong (λ y → (y ⊛ pure f) ⊛ x) (hom A _∘′_ g) ⟩
      ((pure (g ∘′_) ⊛ pure f) ⊛ x)         ≡⟨ cong (_⊛ x) (hom A (_∘′_ g) f) ⟩  
      (pure (g ∘′ f) ⊛ x) ∎ }
      where
        open module X = RawIApplicative (A .rawIA)

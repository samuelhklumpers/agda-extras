{-# OPTIONS --without-K #-}

module Applicatives where

open import Function.Base using (id; _$′_; _∘′_)
open import Effect.Functor using (RawFunctor)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Level renaming (zero to lzero)

open import Functors public


open ≡-Reasoning



private
  variable
    i a b : Level
    A B C : Set a

HIFun : Set i → (a b : Level) → Set (i ⊔ suc a ⊔ suc b)
HIFun I a b = I → I → Set a → Set b


record RawIApplicative' {I : Set i} (F : HIFun I a b) : Set (i ⊔ suc a ⊔ b) where
  infixl 4 _⊛_ 
  field
    pure : ∀ {i} → A → F i i A
    _⊛_  : ∀ {i j k} → F i j (A → B) → F j k A → F i k B

  rawFunctor : ∀ {i j} → RawFunctor (F i j)
  rawFunctor = record { _<$>_ = λ g x → pure g ⊛ x }


record PreIApplicative {I : Set i} (F : HIFun I a b) : Set (i ⊔ suc a ⊔ b) where
  field
    {{RawIApp}} : RawIApplicative' F

  open RawIApplicative' RawIApp using (pure; _⊛_; rawFunctor) public

  field
    a-ident : ∀ {i j} → (v : F i j A)
      → (pure id ⊛ v) ≡ v
      
    a-comp  : ∀ {i j k l} → (u : F i j (B → C)) (v : F j k (A → B)) (w : F k l A)
      → (((pure _∘′_ ⊛ u) ⊛ v) ⊛ w) ≡ (u ⊛ (v ⊛ w))
      
    hom   : ∀ {i} → (f : A → B) (x : A)
      → (pure f ⊛ pure x) ≡ pure {B} {i} (f x)
      
    inter : ∀ {i j} → (u : F i j (A → B)) (y : A)
      → (u ⊛ pure y) ≡ (pure (_$′ y) ⊛ u)


open PreIApplicative {{...}} public

record IApplicative {I : Set i} (F : HIFun I a b) : Set (i ⊔ suc a ⊔ b) where
  constructor iapp
  field
    {{PreIApp}}  : PreIApplicative F
    {{AppFun}}   : {k l : I} → Functor (F k l)
    compatAppFun : {k l : I} → (f : A → B) (x : F k l A) → (f <$> x) ≡ (pure f ⊛ x)  

open IApplicative {{...}} public


module AppToFun {i a b} {I : Set i} (F : HIFun I a b) where
  instance
    preAppToFun : {{PreIApplicative F}} → {k l : I} → Functor (F k l)
    preAppToFun {k = k} {l = l} = record {
      f-ident = a-ident ;
      f-comp  = λ g f x → begin
        (pure g ⊛ (pure f ⊛ x))               ≡⟨ sym (a-comp (pure g) (pure f) x) ⟩
        (((pure _∘′_ ⊛ pure g) ⊛ pure f) ⊛ x) ≡⟨ cong (λ y → (y ⊛ pure f) ⊛ x) (hom _∘′_ g) ⟩
        ((pure (g ∘′_) ⊛ pure f) ⊛ x)         ≡⟨ cong (_⊛ x) (hom (_∘′_ g) f) ⟩  
        (pure (g ∘′ f) ⊛ x) ∎ }
          where
            instance
              appToFun' : RawFunctor (F k l)
              appToFun' = rawFunctor 

    preAppToApp : {{PreIApplicative F}} → IApplicative F
    preAppToApp = iapp λ f x → refl

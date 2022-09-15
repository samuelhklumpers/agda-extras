{-# OPTIONS --without-K --safe #-}

module Help2 where

open import Effect.Functor using (RawFunctor) public
open import Level using (Level; suc; _⊔_) renaming (zero to lzero)
open import Function.Base using (id; _$′_; _∘′_)
open import Effect.Functor renaming (RawFunctor to F0)
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Unit


open ≡-Reasoning

private
  variable
    p a b : Level
    A B C : Set a


HIFun : Set p → (a b : Level) → Set (p ⊔ suc a ⊔ suc b)
HIFun I a b = I → I → Set a → Set b

open F0 {{...}} public

record F1 (F : Set a → Set b) : Set (suc a ⊔ b) where
  field 
    {{rawF}} : F0 F

open F1 {{...}} hiding (rawF) public


record A0 {I : Set p} (F : HIFun I a b) : Set (p ⊔ suc a ⊔ b) where
  infixl 4 _⊛_ 
  field
    pure : ∀ {i} → A → F i i A
    _⊛_  : ∀ {i j k} → F i j (A → B) → F j k A → F i k B


open A0 {{...}} public


record A1 {I : Set p} (F : HIFun I a b) : Set (p ⊔ suc a ⊔ b) where
  field
    {{rawIA}} : A0 F


open A1 {{...}} public


record A2 {I : Set p} (F : HIFun I a b) : Set (p ⊔ suc a ⊔ b) where
  constructor iapp
  field
    {{preIA}}  : A1 F
    {{AF}}   : {k l : I} → F1 (F k l)

  
  fmap' : {F : Set a → Set b} → {{F1 F}} → {A B : Set a} → (A → B) → F A → F B
  fmap' = _<$>_

  field
    compatAppFun : {k l : I} → (f : A → B) (x : F k l A) → (f <$> x) ≡ (pure f ⊛ x)  


open A2 {{...}} public


-- module AppToFun {p a b} {I : Set p} (F : HIFun I a b) where
--   instance
--     preAppToFun : {{PreIApplicative F}} → {k l : I} → Functor (F k l)
--     preAppToFun {k = k} {l = l} = record {
--       f-ident = a-ident ;
--       f-comp  = λ g f x → begin
--         (pure g ⊛ (pure f ⊛ x))               ≡⟨ sym (a-comp (pure g) (pure f) x) ⟩
--         (((pure _∘′_ ⊛ pure g) ⊛ pure f) ⊛ x) ≡⟨ cong (λ y → (y ⊛ pure f) ⊛ x) (hom _∘′_ g) ⟩
--         ((pure (g ∘′_) ⊛ pure f) ⊛ x)         ≡⟨ cong (_⊛ x) (hom (_∘′_ g) f) ⟩  
--         (pure (g ∘′ f) ⊛ x) ∎ }
--           where
--             instance

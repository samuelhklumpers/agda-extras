{-# OPTIONS --without-K --safe #-}

module Help where

open import Effect.Functor using (RawFunctor) public
open import Level using (Level; suc; _⊔_) renaming (zero to lzero)
open import Function.Base using (id; _$′_; _∘′_)
open import Effect.Functor using (RawFunctor)
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Unit


open ≡-Reasoning



private
  variable
    p a b : Level
    A B C : Set a


open RawFunctor {{...}} public


fmap : {F : Set a → Set b} → {{RawFunctor F}} → {A B : Set a} → (A → B) → F A → F B
fmap = _<$>_

record Functor (F : Set a → Set b) : Set (suc a ⊔ b) where
  field 
    {{rawF}} : RawFunctor F
    
  field
    f-ident : (x : F A) → (id <$> x) ≡ x
    f-comp  : (g : B → C) (f : A → B) (x : F A)
          → (g <$> (f <$> x)) ≡ (g ∘′ f <$> x)


open Functor {{...}} hiding (rawF) public


HIFun : Set p → (a b : Level) → Set (p ⊔ suc a ⊔ suc b)
HIFun I a b = I → I → Set a → Set b


record RawIApplicative' {I : Set p} (F : HIFun I a b) : Set (p ⊔ suc a ⊔ b) where
  infixl 4 _⊛_ 
  field
    pure : ∀ {i} → A → F i i A
    _⊛_  : ∀ {i j k} → F i j (A → B) → F j k A → F i k B

  --rawFunctor : ∀ {i j} → RawFunctor (F i j)
  --rawFunctor = record { _<$>_ = λ g x → pure g ⊛ x }


open RawIApplicative' {{...}} public

RawApplicative' : (Set a → Set b) → Set (suc a ⊔ b)
RawApplicative' F = RawIApplicative' {I = ⊤} (λ _ _ → F)


record PreIApplicative {I : Set p} (F : HIFun I a b) : Set (p ⊔ suc a ⊔ b) where
  field
    {{RawIApp}} : RawIApplicative' F

  field
    a-ident : ∀ {i j} → (v : F i j A)
      → (pure id ⊛ v) ≡ v
      
    a-comp  : ∀ {i j k l} → (u : F i j (B → C)) (v : F j k (A → B)) (w : F k l A)
      → (((pure _∘′_ ⊛ u) ⊛ v) ⊛ w) ≡ (u ⊛ (v ⊛ w))
      
    hom   : ∀ {i} → (f : A → B) (x : A)
      → (pure {F = F} {i = i} f ⊛ pure x) ≡ pure (f x)
      
    inter : ∀ {i j} → (u : F i j (A → B)) (y : A)
      → (u ⊛ pure y) ≡ (pure (_$′ y) ⊛ u)


open PreIApplicative {{...}} public

PreApplicative : (Set a → Set b) → Set (suc a ⊔ b)
PreApplicative F = PreIApplicative {I = ⊤} (λ _ _ → F)


record IApplicative {I : Set p} (F : HIFun I a b) : Set (p ⊔ suc a ⊔ b) where
  constructor iapp
  field
    {{PreIApp}}  : PreIApplicative F
    {{AppFun}}   : {k l : I} → Functor (F k l)

  
  fmap' : {F : Set a → Set b} → {{Functor F}} → {A B : Set a} → (A → B) → F A → F B
  fmap' = _<$>_

  field
    --compatAppFun : {A B : Set a} → {k l : I} → (f : A → B) (x : F k l A) → {!fmap {F = F k l} ? ?!} ≡ (pure f ⊛ x)  
    compatAppFun : {k l : I} → (f : A → B) (x : F k l A) → (fmap' f x) ≡ (pure f ⊛ x)  


open IApplicative {{...}} public


Applicative : (Set a → Set b) → Set (suc a ⊔ b)
Applicative F = IApplicative {I = ⊤} (λ _ _ → F)


-- pure' : ∀ {I : Set p} {i : I} {F : HIFun I a b} → {{IApplicative F}} → A → F i i A
-- pure' = pure

-- _⊛'_  : ∀ {I : Set p} {i j k : I} {F : HIFun I a b} → {{IApplicative F}} → F i j (A → B) → F j k A → F i k B
-- _⊛'_ = _⊛_

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

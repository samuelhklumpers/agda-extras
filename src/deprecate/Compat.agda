module Compat where

open import Level
open import Relation.Binary.PropositionalEquality
open import Function.Base

open import Extensionality

open ≡-Reasoning

private
  variable a b c ι : Level

HFun : (a b : Level) → Set (suc a ⊔ suc b)
HFun a b = Set a → Set b

record RF (F : HFun a b) : Set (suc a ⊔ b) where
  field
    fmap : ∀ {A B : Set a} → (A → B) → F A → F B

open RF {{...}} public

record Fun (F : HFun a b) : Set (suc a ⊔ b) where
  field
    Fun-RF : RF F

  private
    instance
      Fun-RF' : RF F
      Fun-RF' = Fun-RF
 
  field
    f-ident : {A : Set a} → (x : F A) → fmap id x ≡ x
    f-comp : {A B C : Set a} → (g : B → C) (f : A → B) (x : F A) → fmap (g ∘′ f) x ≡ fmap g (fmap f x)

open Fun {{...}} public

data Compose (G : HFun b c) (F : HFun a b) (A : Set a) : Set (a ⊔ b ⊔ c) where
  compose : G (F A) → Compose G F A

instance
  RFCompose : {G : HFun b c} {F : HFun a b} → {{RF G}} → {{RF F}} → RF (Compose G F)
  fmap {{RFCompose}} f (compose x) = compose (fmap (fmap f) x)

  FunCompose : {G : HFun b c} {F : HFun a b} → {{Fun G}} → {{Fun F}} → Fun (Compose G F)
  Fun-RF ⦃ FunCompose ⦄ = RFCompose
  f-ident ⦃ FunCompose ⦄ (compose x) = {!!}
  f-comp ⦃ FunCompose ⦄ g f (compose x) = {!!}

HIFun : Set ι → (a b : Level) → Set (ι ⊔ suc a ⊔ suc b)
HIFun I a b = I → I → HFun a b

record RIA {I : Set ι} (F : HIFun I a b) : Set (ι ⊔ suc a ⊔ b) where
  field
    pure : ∀ {i} {A : Set a} → A → F i i A
    _⊛_ : ∀ {i j k} {A B : Set a} → F i j (A → B) → F j k A → F i k B

open RIA {{...}} public

record PIA {I : Set ι} (F : HIFun I a b) : Set (ι ⊔ suc a ⊔ b) where
  field
    overlaps {{PIA-RIA}} : RIA F

open PIA {{...}} public

record IApp {I : Set ι} (F : HIFun I a b) : Set (ι ⊔ suc a ⊔ b) where
  constructor iapp
  field
    overlap {{IApp-PIA}} : PIA F
    overlap {{IApp-Fun}} : {i j : I} → Fun (F i j)

    --compat-IApp-Fun : {A B : Set a} {k l : I} → (f : A → B) (x : F i j A) → fmap f x ≡ (pure f ⊛ x)
    

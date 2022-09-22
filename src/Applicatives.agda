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
open import Cong-Skeletons

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
    ap : ∀ {i j k} → F i j (A → B) → F j k A → F i k B

  _⊛_ : ∀ {i j k} → F i j (A → B) → F j k A → F i k B
  _⊛_ = ap

open RawIApplicative public

RawApplicative : (Set a → Set b) → Set (suc a ⊔ b)
RawApplicative F = RawIApplicative {I = ⊤} (λ _ _ → F)


record IApplicative {I : Set p} (F : HIFun I a b) : Set (p ⊔ suc a ⊔ b) where
  field
    rawIA : RawIApplicative F

  private
    open module X = RawIApplicative rawIA renaming (pure to pureF; _⊛_ to _⊛F_)

  field
    a-ident : ∀ {i j} → (v : F i j A)
      → ((pureF id) ⊛F v) ≡ v
      
    a-comp  : ∀ {i j k l} → (u : F i j (B → C)) (v : F j k (A → B)) (w : F k l A)
      → (((pureF _∘′_ ⊛F u) ⊛F v) ⊛F w) ≡ (u ⊛F (v ⊛F w))
      
    hom   : ∀ {i} → (f : A → B) (x : A)
      → (pureF {i = i} f ⊛F pureF x) ≡ pureF (f x)
      
    inter : ∀ {i j} → (u : F i j (A → B)) (y : A)
      → (u ⊛F pureF y) ≡ (pureF (_$′ y) ⊛F u)


open IApplicative public

Applicative : (Set a → Set b) → Set (suc a ⊔ b)
Applicative F = IApplicative {I = ⊤} (λ _ _ → F)


module AppToFun {p a b} {I : Set p} {F : HIFun I a b} where
  rawATF : RawIApplicative F → {k l : I} → RawFunctor (F k l)
  rawATF A = record { _<$>_ = λ f x → pureF f ⊛F x }
    where
      open RawIApplicative A renaming (pure to pureF; _⊛_ to _⊛F_)

  appToFun : IApplicative F → {k l : I} → Functor (F k l)
  appToFun A = record {
    rawF = rawATF (A .rawIA) ;
    f-ident = a-ident A ;
    f-comp =  λ g f x → begin
      (pureF g ⊛F (pureF f ⊛F x)) ≡⟨ sym (a-comp A (pureF g) (pureF f) x) ⟩
      _⊛F_ ≡[ _⊛F_ ≡[ hom A _∘′_ g ] (pureF f) ] x ⟩
      _⊛F_ ≡[ hom A (_∘′_ g) f ] x ⟩
      pureF (g ∘′ f) ⊛F x ∎ }
      where
        open RawIApplicative (A .rawIA) renaming (pure to pureF; _⊛_ to _⊛F_)

open AppToFun public


comp-hom : ∀ {a b p} {I : Set p} {H' : HIFun I a b} {i j : I} {A B C : Set a} → (H : IApplicative H') → (u : B → A) (v : C → B) (w : H' i j C)
         → ap (H .rawIA) (pure (H .rawIA) u) (ap (H .rawIA) (pure (H .rawIA) v) w) ≡ ap (H .rawIA) (pure (H .rawIA) (u ∘′ v)) w
comp-hom H u v w = trans (sym (a-comp H _ _ _)) (trans (cong (λ s → ap (H .rawIA) (ap (H .rawIA) s (pure (H .rawIA) v)) w) (hom H _ _)) (cong (λ s → ap (H .rawIA) s w) (hom H _ _)))

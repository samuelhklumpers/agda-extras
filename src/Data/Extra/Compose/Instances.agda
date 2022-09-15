{-# OPTIONS --without-K #-}

module Data.Extra.Compose.Instances where

open import Function.Base using (id; _∘′_)
open import Level
open import Relation.Binary.PropositionalEquality
open import Effect.Functor
open import Effect.Monad

open import Functors
open import Applicatives
open import Data.Extra.Compose
open import Extensionality

open ≡-Reasoning

private
  variable
    a b c : Level

CompRawF : {G : Set b → Set c} {F : Set a → Set b} → RawFunctor G → RawFunctor F → RawFunctor (Compose G F)
CompRawF G F = record {
  _<$>_ = λ { f (compose x) → compose (fmap G (fmap F f) x) }
  }

CompF : {G : Set b → Set c} {F : Set a → Set b} → Functor G → Functor F → Functor (Compose G F)
CompF G F = record {
  rawF = CompRawF (G .rawF) (F .rawF) ;
  f-ident = λ { (compose x) → cong compose (trans (cong (λ y → mapG y x) (f-ext (f-ident F))) (f-ident G x)) } ;
  f-comp = λ { g f (compose x) → cong compose (begin
    mapG (mapF g) (mapG (mapF f) x) ≡⟨ f-comp G (mapF g) (mapF f) x ⟩
    mapG (mapF g ∘′ mapF f) x ≡⟨ cong (λ h → mapG h x) (f-ext (f-comp F g f)) ⟩
    mapG (mapF (g ∘′ f)) x  ∎
  ) } }
    where
      open RawFunctor (G .rawF) renaming (_<$>_ to mapG)
      open RawFunctor (F .rawF) renaming (_<$>_ to mapF) 

CompRawA : {G : Set b → Set c} {F : Set a → Set b} → RawApplicative G → RawApplicative F → RawApplicative (Compose G F)
CompRawA G F = record {
  pure = λ x → compose (pureG (pureF x)) ;
  ap = λ { (compose f) (compose x) → compose (mapG _⊛F_ f ⊛G x) }
  }
    where
      open RawIApplicative G renaming (pure to pureG; _⊛_ to _⊛G_)
      open RawIApplicative F renaming (pure to pureF; _⊛_ to _⊛F_)
      open RawFunctor (rawATF G) renaming (_<$>_ to mapG)

{-
CompRawM : {G : Set a → Set a} {F : Set a → Set a} → RawMonad G → RawMonad F → Traversable G → RawMonad (Compose G F)
CompRawM = ?

{-record {
  return = λ x → compose (return (return x)) ;
  _>>=_ = λ { (compose x) f → {!!} } }-}
-}

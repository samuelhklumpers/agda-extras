{-# OPTIONS --without-K #-}

module Representables where

open import Level
open import Relation.Binary.PropositionalEquality
open import Function using (const)
open import Function.Inverse hiding (sym)
open import Function.Equality hiding (const; cong)
open import Data.Unit

open import Extensionality
open import Monads
open import Monads.Instances

open ≡-Reasoning
open Inverse


private
  variable
    a b c : Level
    A B C : Set a


Inv : ∀ f t → Set f → Set t → Set (f ⊔ t)
Inv f t = _↔_ {f} {t}

record PreRepresentable (F : Set a → Set b) : Set (suc a ⊔ b ⊔ suc c) where
  field
    Rep : Set c
    rep : {A : Set a} → Inv b (a ⊔ c) (F A) (Rep → A)

  index : {A : Set a} → F A → Rep → A
  index = Π._⟨$⟩_ (Inverse.to rep)
  tabulate : {A : Set a} → (Rep → A) → F A
  tabulate = Π._⟨$⟩_ (Inverse.from rep)

open PreRepresentable {{...}} public


record Representable (F : Set a → Set b) : Set (suc a ⊔ b ⊔ suc c) where
  field
    {{PreRep}} : PreRepresentable {c = c} F
    {{RepMon}} : PreIMonad {I = ⊤} (λ _ _ → F)

  return' : A → F A
  return' x = return x

  field
    returnTabulate : (x : A) → return' x ≡ tabulate (return x)
    bindTabulate   : (m : F A) (f : A → F B) → (m >>= f) ≡ tabulate (index m >>= λ a → index (f a))

open Representable {{...}} public


module RepToMon {a b c} (F : Set a → Set b) where
  instance
    repToMon : {{PreRepresentable {c = c} F}} → PreIMonad {I = ⊤} (λ _ _ → F)
    repToMon = record {
        left-id  = λ a f → begin
          tabulate (index (tabulate (return a)) >>= λ b → index (f b)) ≡⟨ cong (λ s → tabulate (s >>= λ b → index (f b))) (right-inverse-of rep (return a)) ⟩
          tabulate (return a >>= λ b → index (f b)) ≡⟨ cong (λ s → tabulate s) (left-id a (λ b → index (f b))) ⟩
          tabulate (index (f a)) ≡⟨ left-inverse-of rep (f a) ⟩
          f a ∎ ;
        right-id = λ m → begin
          tabulate (index m >>= λ a → index (tabulate (return a))) ≡⟨ cong (λ s → tabulate (index m >>= s)) (f-ext λ a → right-inverse-of rep (return a)) ⟩
          tabulate (index m >>= return) ≡⟨ cong (λ s → tabulate s) (right-id (index m)) ⟩
          tabulate (index m) ≡⟨ left-inverse-of rep m ⟩
          m ∎ ;
        assoc    = λ m f g → begin
          tabulate (index m >>= λ a → index (tabulate (index (f a) >>= λ b → index (g b)))) ≡⟨ cong (λ s → tabulate (index m >>= s)) (f-ext λ a → right-inverse-of rep (index (f a) >>= λ b → index (g b))) ⟩
          tabulate ((index m >>= λ a → index (f a)) >>= λ b → index (g b)) ≡⟨ cong (λ s → tabulate (s >>= λ b → index (g b))) (sym (right-inverse-of rep (index m >>= λ a → index (f a)))) ⟩
          tabulate (index (tabulate (index m >>= λ a → index (f a))) >>= λ b → index (g b)) ∎ }
      where
        instance
          repToMon' : RawIMonad' {I = ⊤} (λ _ _ → F)
          repToMon' = record {
            return = λ x   → tabulate (return x) ;
            _>>=_  = λ m f → tabulate (index m >>= λ a → index (f a)) }

    preRepToRep : {{PreRepresentable {c = c} F}} → Representable {c = c} F
    preRepToRep = record {
      returnTabulate = λ x → refl ;
      bindTabulate = λ m f → refl }

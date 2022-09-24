{-# OPTIONS --without-K #-}

module Effect.Extra.Representables where

open import Level
open import Relation.Binary.PropositionalEquality
open import Function using (const)
open import Function.Inverse hiding (sym)
open import Function.Equality hiding (const; cong)
open import Data.Unit

open import Data.Extra.Function.Instances
open import Extensionality
open import Effect.Extra.Monads

open ≡-Reasoning
open Inverse


private
  variable
    a b c : Level
    A B C : Set a


Inv : ∀ f t → Set f → Set t → Set (f ⊔ t)
Inv f t = _↔_ {f} {t}

record Representable (F : Set a → Set b) : Set (suc a ⊔ b ⊔ suc c) where
  field
    Rep : Set c
    rep : {A : Set a} → (F A) ↔ (Rep → A)

  index : {A : Set a} → F A → Rep → A
  index = Π._⟨$⟩_ (Inverse.to rep)
  tabulate : {A : Set a} → (Rep → A) → F A
  tabulate = Π._⟨$⟩_ (Inverse.from rep)

open Representable public -- asymmetric...

module RepToMon {a b c} (F : Set a → Set b) where
  repToMon : Representable {c = c} F → Monad F
  repToMon R = record {
      rawM = RRM ;
      left-id = λ a f → begin
        tabulate R (bind FRM (index R (tabulate R (return FRM a))) (λ b → index R (f b))) ≡⟨ cong (λ s → tabulate R (bind FRM s (λ b → index R (f b)))) (right-inverse-of (rep R) (return FRM a)) ⟩
        tabulate R (bind FRM (return FRM a) λ b → index R (f b)) ≡⟨ cong (tabulate R) (left-id FunctionM a (λ b → index R (f b))) ⟩
        tabulate R (index R (f a)) ≡⟨ left-inverse-of (rep R) (f a) ⟩
        f a  ∎ ;
      right-id = λ m → begin
        tabulate R (bind FRM (index R m) (λ a → index R (tabulate R (return FRM a)))) ≡⟨ cong (λ s → tabulate R (bind FRM (index R m) s)) (f-ext λ a → right-inverse-of (rep R) (return FRM a)) ⟩
        tabulate R (bind FRM (index R m) (return FRM)) ≡⟨ cong (λ s → tabulate R s) (right-id FunctionM (index R m)) ⟩
        tabulate R (index R m) ≡⟨ left-inverse-of (rep R) m ⟩
        m ∎ ;
      assoc = λ m f g → begin
        tabulate R (bind FRM (index R m) (λ a → index R (tabulate R (bind FRM (index R (f a)) (λ b → index R (g b))))))
          ≡⟨ cong (λ s → tabulate R (bind FRM (index R m) s)) (f-ext λ a → right-inverse-of (rep R) (bind FRM (index R (f a)) (λ b → index R (g b)))) ⟩
          
        tabulate R (bind FRM (bind FRM (index R m) (λ a → index R (f a))) (λ b → index R (g b)))
          ≡⟨ cong (λ s → tabulate R (bind FRM s (λ b → index R (g b)))) (sym (right-inverse-of (rep R) (bind FRM (index R m) (λ a → index R (f a))))) ⟩
          
        tabulate R (bind FRM (index R (tabulate R (bind FRM (index R m) (λ a → index R (f a))))) (λ b → index R (g b))) ∎ }
        where
          open RawIMonad

          FRM = FunctionRawM

          RRM : RawMonad F
          RRM = record {
            return = λ x   → tabulate R (return FRM x) ;
            _>>=_  = λ m f → tabulate R (bind FRM (index R m) λ a → index R (f a)) }

module AppToFunExample where

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Effect.Applicative.Indexed
open import Effect.Functor
open import Level

open import Extensionality
open import Functors
open import Applicatives


private
  variable
    ℓ : Level
    A B : Set ℓ


→F : Set ℓ → Set ℓ → Set ℓ
→F a b = a → b

→F' : Set ℓ → ⊤ → ⊤ → Set ℓ → Set ℓ
→F' a _ _ = →F a

instance
  →RawApp : RawIApplicative (→F' B)
  →RawApp = record { pure = λ x y → x ; _⊛_ = λ f g x → f x (g x) }

  →PreApp : PreIApplicative (→F' B)
  →PreApp = record {
    a-ident = λ v → f-ext λ x → refl ;
    a-comp = λ u v w → f-ext λ x → refl ;
    hom = λ f x → refl ;
    inter = λ u y → refl }


module Derived where
  private
    open module ATF {ℓ} {B : Set ℓ} = AppToFun (→F' B)

    ex1 : {A B C : Set ℓ} → (B → C) → (A → B) → A → C
    ex1 g f = g <$> f

module Manual where
  private
    instance
      →RawFun : RawFunctor (→F B)
      →RawFun = record { _<$>_ = λ f g x → f (g x) }

      →Fun : Functor (→F B)
      →Fun = record {
        f-ident = λ g → f-ext (λ x → refl) ;
        f-comp = λ h g f → f-ext λ x → refl  }

      →App : IApplicative (→F' B)
      →App = iapp λ f g → refl

    ex1 : {A B C : Set ℓ} → (B → C) → (A → B) → A → C
    ex1 g f = g <$> f

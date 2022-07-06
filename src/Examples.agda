{-# OPTIONS --guardedness --overlapping-instances #-}


module Examples where

open import Relation.Binary.PropositionalEquality
open import Data.Vec as V
open import Level
open import Data.Vec.Properties
open import Data.Nat renaming (suc to succ)
open import Data.Fin using (Fin)
open import Data.Unit
open import Effect.Applicative.Indexed

open import Functors
open import Applicatives
open import Monads
open import Representables
open import Extensionality


private
  variable
    ℓ : Level
    A B : Set ℓ


module VecEx where
  Vec' : ℕ → Set ℓ → Set ℓ 
  Vec' n A = Vec A n


  instance
    VecRep : ∀ {n ℓ} → Representable {ℓ = ℓ} (Vec' n)
    VecRep {n} = record {
      Rep = Fin n ;
      iso = λ A → record {
        to = lookup ;
        from = V.tabulate ;
        retract = λ v → tabulate∘lookup v ;
        section = section' } }
          where
            section' : {A : Set ℓ} → (f : Fin n → A) → lookup (V.tabulate f) ≡ f
            section' f = f-ext (λ i → lookup∘tabulate f i)

  ex1 : Vec ℕ 2
  ex1 = (_+ 1) <$> 0 ∷ 1 ∷ []

  test1 : ex1 ≡ 1 ∷ 2 ∷ []
  test1 = refl


module FunAppEx where
  FunF : Set ℓ → Set ℓ → Set ℓ
  FunF a b = a → b

  FunF' : Set ℓ → ⊤ → ⊤ → Set ℓ → Set ℓ
  FunF' a _ _ = FunF a

  instance
    RawAppFun : RawIApplicative (FunF' B)
    RawAppFun = record { pure = λ x y → x ; _⊛_ = λ f g x → f x (g x) }

  instance
    AppFun : IApplicative (FunF' B)
    AppFun = record {
      a-ident = λ v → f-ext λ x → refl ;
      a-comp = λ u v w → f-ext λ x → refl ;
      hom = λ f x → refl ;
      inter = λ u y → refl }


  ex1 : {A B C : Set ℓ} → (B → C) → (A → B) → A → C
  ex1 g f = g <$> f

{-# OPTIONS --guardedness #-}


module Examples where

open import Relation.Binary.PropositionalEquality
open import Data.Vec as V
open import Level
open import Data.Vec.Properties
open import Data.Nat renaming (suc to succ)
open import Function.Inverse
open import Data.Fin using (Fin)
open import Data.Unit

open import Functors
open import Applicatives
open import Monads
open import Representables
open import Extensionality


private
  variable
    a : Level
    A B : Set a


module VecEx where
  Vec' : ℕ → Set a → Set a 
  Vec' n A = Vec A n

  instance
    VecRep : ∀ {n a} → PreRepresentable {a = a} (Vec' n)
    VecRep {n} = record {
      Rep = Fin n ;
      rep = inverse lookup V.tabulate (λ v → tabulate∘lookup v) (λ f → f-ext (λ i → lookup∘tabulate f i)) }

  
  open module RTM {n a} = RepToMon {a = a} {c = 0ℓ} (Vec' n)
  open module MTA {n a} = MonToApp {a = a} {I = ⊤} (λ _ _ → Vec' n)
  open module ATF {n a} = AppToFun {a = a} {I = ⊤} (λ _ _ → Vec' n)

  ex1 : Vec ℕ 2
  ex1 = (_+ 1) <$> 0 ∷ 1 ∷ []

  test1 : ex1 ≡ 1 ∷ 2 ∷ []
  test1 = refl

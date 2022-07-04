module Examples where

open import Lawful
open import Representables

open import Relation.Binary.PropositionalEquality
open import Data.Vec
open import Level
open import Data.Vec.Properties
open import Data.Nat
open import Data.Fin using (Fin)


module VecEx where
  Vec' : ∀ {ℓ} → ℕ → Set ℓ → Set ℓ 
  Vec' n A = Vec A n


  instance
    VecRep : ∀ {n : ℕ} {ℓ} → Representable {ℓ} (Vec' n)
    VecRep {n} = record {
      Rep = Fin n ;
      iso = λ A → record {
        to = lookup ;
        from = tabulate ;
        retract = λ v → tabulate∘lookup v ;
        section = λ f → f-ext (λ i → lookup∘tabulate f i) } }

  open Representable {0ℓ} {0ℓ} {Vec' 2} VecRep
  
  ex1 : ((_+ 1) <$> 0 ∷ 1 ∷ []) ≡ 1 ∷ 2 ∷ []
  ex1 = refl
  

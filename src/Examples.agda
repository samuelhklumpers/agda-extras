module Examples where

open import Relation.Binary.PropositionalEquality
open import Data.Vec
open import Level
open import Data.Vec.Properties
open import Data.Nat
open import Data.Fin using (Fin)

open import Functors
open import Applicatives
open import Monads
open import Representables
open import Extensionality


private
  variable
    ℓ : Level


module VecEx where
  Vec' : ℕ → Set ℓ → Set ℓ 
  Vec' n A = Vec A n


  instance
    VecRep : ∀ {n ℓ} → Representable {ℓ = ℓ} (Vec' n)
    VecRep {n} = record {
      Rep = Fin n ;
      iso = λ A → record {
        to = lookup ;
        from = tabulate ;
        retract = λ v → tabulate∘lookup v ;
        section = section' } }
          where
            section' : {A : Set ℓ} → (f : Fin n → A) → lookup (tabulate f) ≡ f
            section' f = f-ext (λ i → lookup∘tabulate f i)


  open module IR {ℓ} {n} = Representable {ℓ = ℓ} (VecRep {n = n})

  ex1 : Vec ℕ 2
  ex1 = (_+ 1) <$> 0 ∷ 1 ∷ []

  test1 : ex1 ≡ 1 ∷ 2 ∷ []
  test1 = refl


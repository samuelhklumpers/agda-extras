module Monads where

open import Effect.Monad

open import Categories.Category.Instance.Sets
import Categories.Functor as Funct
import Categories.NaturalTransformation as Nat
import Categories.Monad as Mon

open Mon.Monad

concreteMonad : ∀ {o} → (M : Mon.Monad (Sets o)) → RawMonad (F.F₀ M)
concreteMonad {o} M@record { F = F ; η = record { η = η ; commute = _ ; sym-commute = _ } ; μ = record { η = μ ; commute = _ ; sym-commute = _ } ; assoc = _ ; sym-assoc = _ ; identityˡ = _ ; identityʳ = _ } = record {
  return = return ;
  _>>=_ =  bind } where
    return : {A : Set o} → A → F.F₀ M A
    return {A} x = η A x

    bind : {A B : Set o} → F.F₀ M A → (A → F.F₀ M B) → F.F₀ M B
    bind {A} {B} x f = μ B (F.F₁ M f x)

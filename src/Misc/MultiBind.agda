module MultiBind where

open import Level
open import Effect.Monad
open import Data.Nat
open import Data.List

module HetList (f : Level) where
  data HList : List (Set f) → Set f where
    ε    : HList []
    _::_ : ∀ {A L} → (a : A) → HList L → HList (A ∷ L)

  Fun : List (Set f) → Set f → Set f
  Fun []       r = r
  Fun (a ∷ as) r = a → Fun as r

  uncurry : ∀ {as} {r} → Fun as r → HList as → r
  uncurry f ε          = f
  uncurry f (x :: xs) = uncurry (f x) xs

  curry : ∀ {as} {r} → (HList as → r) → Fun as r
  curry {[]}     f = f ε
  curry {a ∷ as} f = λ x → curry (λ xs → f (x :: xs))

module Binds (f : Level) {M : Set f → Set f} (Mon : RawMonad M) where
  open RawMonad Mon
  open HetList f

  sequence : ∀ {as} → HList (map M as) → M (HList as)
  sequence {[]}     ε         = return ε
  sequence {a ∷ as} (x :: xs) = do
      y  ← x
      ys ← sequence xs
      return (y :: ys)

  bind' : ∀ {as} {r} → (HList as → (M r)) → HList (map M as) → (M r)
  bind' f xs = sequence xs >>= f

  bind : ∀ {as} {r} → Fun as (M r) → Fun (map M as) (M r)
  bind f = curry (bind' (uncurry f))


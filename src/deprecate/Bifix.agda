module Bifix where

open import Effect.Extra.Monads
open import Effect.Extra.Comonads
open import Effect.Extra.Functors

open import Extensionality

open import Function.Base
open import Relation.Binary.PropositionalEquality


open ≡-Reasoning

private variable
  A B : Set

module _ (M : Set → Set) (W : Set → Set) (Mon : Monad M) (Com : Comonad W) where
  open RawComonad (Com .rawW)
  open RawIMonad (Mon .rawM)

  {-# TERMINATING #-}
  fix : (A → A) → A
  fix f = f (fix f)

  {-# TERMINATING #-}
  cofix : W (W A → A) -> A
  cofix w = extract w (extend cofix w)

  {-# TERMINATING #-}
  mfix : (A → M A) → M A
  mfix f = mfix f >>= f

  mapM : (A → B) → M A → M B
  mapM f = _>>= return ∘' f

  mapW : (A → B) → W A → W B
  mapW f = extend (f ∘' extract)

  module _ (distr : W (M A) → M (W A)) where
    bifix-1 : W (W A → M A) → M A
    bifix-1 f = cofix (mapW ((_∘' distr) ∘' flip _>>=_) f)

    bifix-2 : W (W A → M A) → M A
    bifix-2 f = mapM extract (extract (mapW (mfix ∘' (distr ∘'_) ∘' extend) f))

    bifix-1a : W (W A → M A) → M A
    bifix-1a f = extract (fix {!extend (λ x → distr x >>= extract f)!})

    bifix-1b : W (W A → M A) → M A
    bifix-1b f = distr (fix (extend (λ x → distr x >>= extract f))) >>= extract f

    bifix-2a : W (W A → M A) → M A
    bifix-2a f = fix (_>>= distr ∘' extend (extract f)) >>= return ∘' extract

    bifix-2b : W (W A → M A) → M A
    bifix-2b f = (fix (_>>= (λ x → distr (extend (extract f) x))) >>= (λ x → distr (extend (extract f) x))) >>= return ∘' extract

    bifix-2c : W (W A → M A) → M A
    bifix-2c f = fix (_>>= (λ x → distr (extend (extract f) x))) >>= λ y → mapM extract (distr (extend (extract f) y))

    need : (W (W A → M A)) → Set
    need f = ∀ x → (extract f x ≡ mapM extract (distr (extend (extract f) x)))

    -- distr (extend f x) : M (W A)
    -- extend f x : W (M A)
    -- f : W B → M A
    -- x : W B

    -- mapM extract (distr (extend f x)) = f x

    -- example:
    -- f : NonEmpty B → Maybe A
    -- x : NonEmpty B
    
    {- case x of
         (Nil := y) ->
           extend f x = Nil := f x
           distr (Nil := f x)
           case f x
             Nothing ->
               distr (Nil := f x) = Nothing
               mapMaybe extract Nothing = Nothing
             Just y ->
               distr (Nil := f x) = Just (Nil := y)
               mapMaybe extract (Just (Nil := y)) = Just y
         (zs :> z := y) ->
           extend f x = extendL f zs :> f (zs := z) := f x
           distr (extendL f zs :> f (zs := z) := f x)
           case f x
             Nothing ->
               distr (extendL f zs :> f (zs := z) := f x) = Nothing
               Nothing
             Just y ->
               distr (extendL f zs :> f (zs := z) := f x) = Just (catMaybes (extendL f zs :> f (zs := z)) := y)
               Just y -- nice
    -}

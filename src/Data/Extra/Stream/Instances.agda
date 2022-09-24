{-# OPTIONS --guardedness #-}

module Data.Extra.Stream.Instances where

open import Codata.Guarded.Stream as S
open import Effect.Functor
open import Function.Base using (_∘′_; const)
open import Level
open import Relation.Binary.PropositionalEquality

open import Effect.Extra.Functors
open import Effect.Extra.Applicatives
open import Effect.Extra.Monads hiding (bind)
-- open import Effect.Extra.Traversables


private
  variable
    a b c : Level
    A : Set a
    B : Set b


StreamRawF : RawFunctor {ℓ = a} Stream
StreamRawF = record
  { _<$>_ = map
  }

StreamF : Functor {a = a} Stream
StreamF = record
  { rawF = StreamRawF
  ; f-ident = λ x → {!cubical!}
  ; f-comp = λ g f x → {!!}
  }

StreamRawA : RawApplicative {a = a} Stream
StreamRawA = record
  { pure = repeat
  ; ap = S.ap }

StreamA : Applicative {a = a} Stream
StreamA = record
  { rawIA = StreamRawA
  ; a-ident = λ v → {!!}
  ; a-comp = λ u v w → {!!}
  ; hom = λ f x → {!!} ;
  inter = λ u y → {!!} } 

diagonal : Stream (Stream A) → Stream A
head (diagonal xs) = head (head xs)
tail (diagonal xs) = diagonal (fmap StreamRawF tail (tail xs))

bind : {A B : Set a} → Stream A → (A → Stream B) → Stream B
bind xs f = diagonal (fmap StreamRawF f xs)

StreamRawM : RawMonad {a = a} Stream
StreamRawM = record
  { return = repeat
  ; _>>=_ = bind }

StreamM : Monad {a = a} Stream
StreamM = record
  { rawM = StreamRawM
  ; left-id = {!!}
  ; right-id = {!!}
  ; assoc = {!!} }





-- TODO

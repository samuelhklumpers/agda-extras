module Unfinished where

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Level
open import Function.Base using (id)

open import Extensionality
open import Effect.Extra.Functors
open import Effect.Extra.Applicatives
open import Effect.Extra.Monads
open import Effect.Extra.Functors.Instances


private
  variable
    a b c : Level
    A : Set a
    B : Set b

join : {F : Set a → Set a} → {{_ : Monad F}} → {A : Set a} → F (F A) → F A
join x = x >>= id

lemma : {G F : Set a → Set a} → {{_ : Monad G}} → {{_ : Monad F}} → {{_ : Monad (Compose G F)}} → {A : Set a} → Compose F G A → Compose G F A
lemma (compose x) = join (compose (fmap {{rawFunctor}} (fmap {{rawFunctor}} compose) (return (fmap {{rawFunctor}} (fmap {{rawFunctor}} return) x))))

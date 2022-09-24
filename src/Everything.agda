{-# OPTIONS --guardedness #-}

module Everything where

open import Data.Extra.Compose
open import Data.Extra.Compose.Instances
open import Data.Extra.Const
open import Data.Extra.Const.Instances
open import Data.Extra.Function.Instances
open import Data.Extra.Identity
open import Data.Extra.Identity.Instances
open import Data.Extra.List.Instances
open import Data.Extra.Stream.Instances

open import Effect.Extra.Applicatives
open import Effect.Extra.Applicatives.Solver
open import Effect.Extra.Foldables
open import Effect.Extra.Functors
open import Effect.Extra.Monads
open import Effect.Extra.Representables
open import Effect.Extra.Traversables

open import Structures.Monoids
open import Structures.Semigroups

open import Misc.Cong-Reasoning
open import Extensionality

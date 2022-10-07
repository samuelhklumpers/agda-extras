module Data.Extra.Normal.Instances where

open import Level
open import Data.List
open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

open import Data.Extra.Compose
open import Data.Extra.Compose.Instances
open import Data.Extra.Identity
open import Data.Extra.Identity.Instances
open import Effect.Extra.Applicatives
open import Effect.Extra.Applicatives.Solver
open import Effect.Extra.Traversables
open import Misc.Cong-Reasoning


private
  variable 
    a b : Level


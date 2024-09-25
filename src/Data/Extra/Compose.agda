{-# OPTIONS --cubical-compatible #-}

module Data.Extra.Compose where

open import Level

private
  variable
    a b c : Level


record Compose (G : Set b → Set c) (F : Set a → Set b) (A : Set a) : Set (a ⊔ b ⊔ c) where
  constructor compose
  field
    runCompose : G (F A)
    
open Compose public



{-# OPTIONS --without-K --safe #-}

module Data.Extra.Identity where

open import Level

private
  variable
    a : Level


record Identity (A : Set a) : Set a where
  constructor identity
  field
    runIdentity : A
    
open Identity public

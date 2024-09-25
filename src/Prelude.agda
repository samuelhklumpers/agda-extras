{-# OPTIONS --cubical-compatible --safe #-}

module Prelude where

open import Function.Base using (id; _∘′_; const; _$_) public
open import Level renaming (zero to lzero; suc to lsuc) public
open import Relation.Binary.PropositionalEquality public

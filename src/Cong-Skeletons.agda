{-# OPTIONS --without-K --safe #-}

module Cong-Skeletons where

open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


private
  variable
    a b c : Level
    A B C : Set a
    

_≡[_⟩_ : {x y : A} {z : B} → (f : A → B) → x ≡ y → f y ≡ z → f x ≡ z 
f ≡[ x≡y ⟩ fy≡z = trans (cong f x≡y) fy≡z

≡⟨_]_⟩_ : {f g : A → B} {z : B} → f ≡ g → (x : A) → g x ≡ z → f x ≡ z
≡⟨ f≡g ] x ⟩ gx≡z  = trans (cong (λ f → f x) f≡g) gx≡z

_≡[_]_⟩_ : {x y : A} {w : C} → (f : A → B → C) → x ≡ y → (z : B) → f y z ≡ w → f x z ≡ w
f ≡[ x≡y ] z ⟩ fyz≡w = trans (cong (λ x → f x z) x≡y) fyz≡w 

infixr 2 _≡[_⟩_ ≡⟨_]_⟩_ _≡[_]_⟩_

test : {x y : A} {z : B} {w : C} → (f : A → B) → (x y : A) (z w : B) → x ≡ y → f y ≡ z → z ≡ w → f x ≡ w  
test f x y z w x≡y fy≡z z≡w = begin
  f ≡[ x≡y ⟩
  f y ≡⟨ fy≡z ⟩
  z ≡⟨ z≡w ⟩
  w ∎

_≡[_> : {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
f ≡[ x≡y > = cong f x≡y

≡<_]_ : {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
≡< f≡g ] x  = cong (λ f → f x) f≡g

_≡[_]_ : {x y : A} → (f : A → B → C) → x ≡ y → (z : B) → f x z ≡ f y z
f ≡[ x≡y ] z = cong (λ x → f x z) x≡y

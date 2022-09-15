{-# OPTIONS --sized-types #-}

module AppSolver where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat renaming (_⊔_ to _⊔ⁿ_)
open import Data.Product
open import Function.Base using (_$′_; _∘′_)

{-
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : A → List A → List A

data HList {a} : List (Set a)  → Set a where
  []ₕ  : HList []
  _∷ₕ_ : ∀ {x xs} → (a : x) → HList xs → HList (x ∷ xs)

Fun : ∀ {a} → List (Set a) → Set a → Set a
Fun []       y = y
Fun (x ∷ xs) y = x → Fun xs y

UFun : ∀ {a} → List (Set a) → Set a → Set a
UFun xs x = HList xs → x

uncurry : ∀ {a xs} {x : Set a} → Fun xs x → HList xs → x
uncurry f []ₕ = f
uncurry f (x ∷ₕ xs) = uncurry (f x) xs
-}

private
  variable
    a b : Level
    A B : Set a

data AType (a : Level) : Set (lsuc a) where
  [_] : Set a → AType a
  F₀ : AType a → AType a 
  _⇒_ : AType a → AType a → AType a

private
  variable
    r s t : AType a

-- #Applicative layers × #Positive arrows
tsize : AType a → ℕ × ℕ
tsize [ x ] = 0 , 0
tsize (F₀ t) with tsize t
...| x , y = suc x , y
tsize (t ⇒ s) with tsize s
...| x , y = x , suc y


{-# NO_POSITIVITY_CHECK #-}
data FreeA {a} : AType a → Set (lsuc a) where
  Raw : A → FreeA [ A ]
  Pure : FreeA t → FreeA (F₀ t)
  Fun : (FreeA t → FreeA s) → FreeA (t ⇒ s)
  _◯_ : FreeA (F₀ (t ⇒ s)) → FreeA (F₀ t) → FreeA (F₀ s)

record Count (A : Set) : Set where
  constructor count
  field
    top : A
    num : ℕ

-- Count (Right applications) × Count (Size of type)
size : (t : AType a) → FreeA t → Count ℕ × Count (ℕ × ℕ)
size t (u ◯ v) = {!!}
size t p = count 0 0 , count (tsize t) 1

$ : FreeA t → FreeA ((t ⇒ s) ⇒ s)
$ x = Fun λ { (Fun f) → f x }

o : FreeA ((s ⇒ t) ⇒ ((r ⇒ s) ⇒ (r ⇒ t)))
o = Fun λ { (Fun g) → Fun λ { (Fun f) → Fun λ x → g (f x) } }

simplify : FreeA t → FreeA t
simplify (Pure (Fun f) ◯ Pure x) = Pure (f x)
simplify (u ◯ Pure v) = (Pure ($ v)) ◯ u
simplify (u ◯ (v ◯ w)) = ((Pure o ◯ u) ◯ v) ◯ w 
simplify x = x

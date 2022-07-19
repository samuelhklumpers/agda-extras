{-# OPTIONS --guardedness #-}

open import Data.Unit
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.List as L
open import Data.Empty
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.String as S
open import Data.String.Properties
open import Effect.Monad.Indexed


module FileHandleEx where

-- Indexed monad example for opening and closing files safely
-- 1. let's not pay attention to what happens if you open the same thing twice
-- 2. let's pretend Strings are nice file handles
-- 3. suppose fn ∈ i is an instance argument


H = List String
U = H → H

data _∈_ {A : Set} (x : A) : List A → Set where
  hd : ∀ {xs}                → x ∈ (x ∷ xs)
  tl : ∀ {y xs} (_ : x ∈ xs) → x ∈ (y ∷ xs)

_∈?_ : (x : String) (xs : List String) → Dec (x ∈ xs)
x ∈? []       = no (λ ())
x ∈? (y ∷ xs) with x ≈? y
... | no ¬p = map′ tl h (x ∈? xs)
  where
    h : x ∈ (y ∷ xs) → x ∈ xs
    h hd      = ⊥-elim (¬p (≈-refl {x = x}))
    h (tl pf) = pf
... | yes p with ≈⇒≡ {x = x} {y = y} p
... | refl = yes hd

instance
  In : ∀ {x xs} → {True (x ∈? xs)} → x ∈ xs
  In {x} {xs} {t} with x ∈? xs
  ... | yes p = p


data HCom : H → H → Set where
  openc   : ∀ {i} (fn : String) → HCom i (fn ∷ i)
  readc   : ∀ {i} (fn : String) → {{p : fn ∈ i}} → HCom i i 
  closec  : ∀ {i} (fn : String) → HCom (fn ∷ i) i

data Free {I : Set} (C : I → I → Set) (R : ∀ {i j} → C i j → Set) : I → I → Set → Set where
  ‵return : ∀ {i A}     → A                                    → Free C R i i A
  _‵>>=_  : ∀ {i j k A} → (c : C i j) → (R c → Free C R j k A) → Free C R i k A

hcomResp : ∀ {i j} → HCom i j → Set
hcomResp (openc fn)   = ⊤
hcomResp (readc fn) = String
hcomResp (closec fn)  = ⊤

Handled = Free {I = H} HCom hcomResp


openf : ∀ {i} (fn : String) → Handled i (fn ∷ i) ⊤ 
openf fn = openc fn ‵>>= ‵return 

readf : ∀ {i} (fn : String) → {{fn ∈ i}} → Handled i i String
readf fn {{p}} = readc fn {{p = p}} ‵>>= ‵return

closef : ∀ {i} (fn : String) → Handled (fn ∷ i) i ⊤
closef fn = closec fn ‵>>= ‵return

instance
  FreeRawMon : ∀ {I} {C : I → I → Set} {R : ∀ {i j} → C i j → Set} → RawIMonad (Free C R)
  FreeRawMon {I} {C} {R} = record {
    return = ‵return ;
    _>>=_  = bind' }
      where
        bind' : ∀ {A B i j k} → Free C R i j A → (A → Free C R j k B) → Free C R i k B
        bind' (‵return x) f = f x
        bind' (c ‵>>= g)  f = c ‵>>= (λ x → bind' (g x) f)

open module FRM {I} {C : I → I → Set} {R : ∀ {i j} → C i j → Set} = RawIMonad (FreeRawMon {C = C} {R = R})

--interpret : ∀ {A} → Handled [] [] A → IO A
--interpret = ?

good : Handled [] [] String
good = do
  openf  "example.txt"
  text ← readf "example.txt"
  closef "example.txt"
  return text

{-
bad1 : Handled [] [] String
bad1 = do
  openf  "example.txt"
  text ← readf "example.txt"
  return text
-}  

{-
bad2 : Handled [] [] String
bad2 = do
  openf  "example.txt"
  text ← readf "example.txt"
  closef "example.txt"
  text ← readf "example.txt"
  return text
-}

{-# OPTIONS --guardedness --cubical #-}

module CubicalExamples where

open import Agda.Builtin.Cubical.Path
open import Cubical.Data.Equality using (pathToEq)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)

open import Level
open import Data.Nat renaming (suc to succ)
open import Data.Unit
open import Data.List using (List; []; _∷_)
open import Function.Inverse
--open import Relation.Binary.PropositionalEquality

open import Extensionality
open import Representables
open import Monads
open import Applicatives
open import Functors


private
  variable
    a : Level
    A : Set a


record Stream (A : Set a) : Set a where
  constructor _⇉_
  coinductive
  field
    hd : A
    tl : Stream A

open Stream

record _≈_ {A : Set a} (x y : Stream A) : Set a where
  coinductive
  field
    hd-≈ : hd x ≡ hd y
    tl-≈ : tl x ≈ tl y

open _≈_

bisim : {x y : Stream A} → x ≈ y → x ≡ y
hd (bisim p i) = hd-≈ p i
tl (bisim p i) = bisim (tl-≈ p) i

ix : Stream A → ℕ → A
ix s 0        = hd s
ix s (succ i) = ix (tl s) i

gen : (ℕ → A) → Stream A
hd (gen f) = f 0
tl (gen f) = gen (λ i → f (succ i))

take : ℕ → Stream A → List A
take zero     s = []
take (succ n) s = hd s ∷ take n (tl s)

instance
  StreamRep : PreRepresentable {a = a} {c = 0ℓ} Stream
  StreamRep = record {
    Rep = ℕ ;
    rep = inverse lookup generate section retract }
      where
        lookup : Stream A → ℕ → A
        lookup s zero     = hd s
        lookup s (succ i) = lookup (tl s) i

        generate : (ℕ → A) → Stream A
        hd (generate f) = f 0
        tl (generate f) = generate (λ x → f (succ x))

        sec : (x : Stream A) → generate (lookup x) ≈ x
        hd-≈ (sec x) = λ _ → hd x
        tl-≈ (sec x) = sec (tl x)

        section : (x : Stream A) → generate (lookup x) == x
        section x = pathToEq (bisim (sec x))

        ret : (f : ℕ → A) → (i : ℕ) → lookup (generate f) i == f i
        ret f 0        = refl
        ret f (succ i) = ret (λ x → f (succ x)) i

        retract : (f : ℕ → A) → lookup (generate f) == f
        retract f = f-ext (ret f)

open module RTM {a} = RepToMon {a = a} {c = 0ℓ} Stream
open module MTA {a} = MonToApp {a = a} {I = ⊤} (λ _ _ → Stream)
open module ATF {a} = AppToFun {a = a} {I = ⊤} (λ _ _ → Stream)

count : Stream ℕ
count = tabulate (λ x → x)

ex1 : Stream ℕ
ex1 = (λ x → x * x) <$> count

ex2 : Stream ℕ
ex2 = ((λ x y → x * y) <$> count) ⊛ count

{-
test1 : ex1 ≈ ex2
hd-≈ test1 = λ _ → 0
tl-≈ test1 = {!:(!}
-}

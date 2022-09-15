{-# OPTIONS --guardedness #-}


module Examples where

open import Relation.Binary.PropositionalEquality
open import Data.Vec as V hiding (_⊛_)
open import Level
open import Data.Vec.Properties
open import Data.Nat renaming (suc to succ)
open import Function.Inverse
open import Data.Fin using (Fin)
open import Data.Unit
open import Function.Base using (_∘′_)

open import Functors
open import Functors.Instances
open import Applicatives
open import Monads
open import Monads.Instances
open import Representables
open import Traversables
open import Extensionality


private
  variable
    a b : Level
    A B : Set a


module VecEx where
  Vec' : ℕ → Set a → Set a 
  Vec' n A = Vec A n

  instance
    VecRep : ∀ {n a} → PreRepresentable {a = a} (Vec' n)
    VecRep {n} = record {
      Rep = Fin n ;
      rep = inverse lookup V.tabulate (λ v → tabulate∘lookup v) (λ f → f-ext (λ i → lookup∘tabulate f i)) }

  
  open module RTM {n a} = RepToMon {a = a} {c = 0ℓ} (Vec' n)
  open module MTA {n a} = MonToApp {a = a} {I = ⊤} (λ _ _ → Vec' n)
  open module ATF {n a} = AppToFun {a = a} {I = ⊤} (λ _ _ → Vec' n)

  ex1 : Vec ℕ 2
  ex1 = fmap' (_+ 1) (0 ∷ 1 ∷ [])

  ex2 : Vec ℕ 2
  ex2 = ((_+ 1) ∷ (_+ 2) ∷ []) ⊛' (0 ∷ 1 ∷ [])

  test1 : ex1 ≡ 1 ∷ 2 ∷ []
  test1 = refl


module ListEx where
  open import Data.List as L

  traverseList : {F : Set a → Set b} → {{RawApplicative' F}} → (A → F B) → List A → F (List B)
  traverseList f [] = pure []
  traverseList {F = F} f (x ∷ xs) = fmap {{rawFunctor}} L._∷_ (f x) ⊛ traverseList f xs

  instance
    ListRTrav : ∀ {n} → RawTraversable {a = n} List
    ListRTrav = record { traverse = traverseList }

    ListTrav : ∀ {n} → PreTraversable {a = n} List
    ListTrav = record {
      t-nat = t-nat' ;
      t-ident = t-ident' ;
      t-comp = t-comp' }
      where
        t-nat' : ∀ {a b} {A B : Set a} (t : AppTrans') {F G : Set a → Set b} (f : A → F B) →
                    {{_ : Applicative F}} → {{_ : Applicative G}} → AppTrans'' {a = a} {b = b} t →
                    (x : List A) → t {F = F} {G = G} (traverse f x) ≡ traverse (t {F = F} {G = G} ∘′ f) x
        t-nat' t f p [] = t-pure p []
        t-nat' t f p (x ∷ xs) = trans
          (t-ap p (traverse f xs) (fmap {{rawFunctor}} L._∷_ (f x)))
          {!!}
          -- (t-nat' {!t!} f {!p!} {!xs!}) 
        
        t-ident' : ∀ {n} {A : Set n} (x : List A) → traverseList {{idPreApp . RawIApp}} identity x ≡ identity x
        t-ident' xs = {!!}

        t-comp' : ∀ {n} {B C A : Set n} {G F : Set n → Set n}
                  ⦃ _ = z : Applicative G ⦄ ⦃ _ = z₁ : Applicative F ⦄ (g : B → G C)
                  (f : A → F B) (x : List A) →
                  RawTraversable.traverse ListRTrav (compose ∘′ (fmap' g ∘′ f)) x ≡ compose (fmap' (RawTraversable.traverse ListRTrav g) (RawTraversable.traverse ListRTrav f x))
        t-comp' g f xs = {!!}


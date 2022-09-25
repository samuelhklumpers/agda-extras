module Data.Extra.List.Instances where

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
open import Extensionality
open import Misc.Cong-Reasoning


private
  variable 
    a b : Level


ListRawTr : ∀ {a b} → RawTraversable {a} {b} List
traverse ListRawTr A f []       = pure A []
traverse ListRawTr A f (x ∷ xs) = ap A (fmap (rawATF A) _∷_ (f x)) (traverse ListRawTr A f xs)

ListTr : ∀ {a} → Traversable {a} List
ListTr = record
  { rawT = ListRawTr
  ; t-nat = nat
  ; t-ident = ident
  ; t-comp = comp
  }
    where
      nat : ∀ {a} {b} {A B : Set a} {F' G' : Set a → Set b} (t : RawAppTrans F' G') (f : A → F' B)
            (F : Applicative F') (G : Applicative G') → AppTrans t → (x : List A) →
            t F G (traverse ListRawTr (F .rawIA) f x) ≡ traverse ListRawTr (G .rawIA) (t F G ∘′ f) x
      nat t f F G T [] = t-pure T F G []
      nat t f F G T (x ∷ xs) = begin
        t F G (ap (F .rawIA) (fmap (rawATF (F .rawIA)) _∷_ (f x)) (traverse ListRawTr (F .rawIA) f xs))
          ≡⟨ t-ap T F G (traverse ListRawTr (F .rawIA) f xs) (fmap (rawATF (F .rawIA)) _∷_ (f x)) ⟩

        ap (G .rawIA) (t F G (fmap (rawATF (F .rawIA)) _∷_ (f x))) ≡[ nat t f F G T xs ⟩
        ap (G .rawIA) ≡[ t-ap T F G (f x) (pure (F .rawIA) _∷_) ] (traverse ListRawTr (G .rawIA) (t F G ∘′ f) xs) ⟩
        ap (G .rawIA) ≡[ ap (G .rawIA) ≡[ t-pure T F G _∷_ ] (t F G (f x)) ] (traverse ListRawTr (G .rawIA) (t F G ∘′ f) xs) ⟩
        traverse ListRawTr (G .rawIA) (t F G ∘′ f) (x ∷ xs)  ∎
  
      ident : ∀ {a} {A : Set a} (x : List A) → traverse ListRawTr IdRawA identity x ≡ identity x
      ident [] = refl
      ident (x ∷ xs) = begin
        identity (_∷_ x (runIdentity (traverse ListRawTr IdRawA identity xs))) ≡⟨⟩
        identity ≡[ _∷_ x ≡[ runIdentity ≡[ ident xs > > ⟩
        identity (x ∷ xs) ∎
      
      comp : ∀ {a} {B C A : Set a} {G' F' : Set a → Set a} (G : Applicative G') (F : Applicative F') (g : B → G' C) (f : A → F' B) (xs : List A) →
             traverse ListRawTr (CompRawA (F .rawIA) (G .rawIA)) (compose ∘′ fmap (rawATF (F .rawIA)) g ∘′ f) xs
             ≡ compose (fmap (rawATF (F .rawIA)) (traverse ListRawTr (G .rawIA) g) (traverse ListRawTr (F .rawIA) f xs))
      comp G F g f [] = begin
        compose (pure (F .rawIA) (pure (G .rawIA) [])) ≡⟨⟩
        compose ≡[ sym (hom F (traverse ListRawTr (G .rawIA) g) []) ⟩
        compose (fmap (rawATF (F .rawIA)) (traverse ListRawTr (G .rawIA) g) (traverse ListRawTr (F .rawIA) f [])) ∎
      comp {B = B} {C = C} {A = A} {G' = G'} {F' = F'} G F g f (x ∷ xs) = cong compose (begin 
        apF (apF (pureF apG) (apF (apF (pureF apG) (pureF (pureG _∷_))) (apF (pureF g) (f x)))) ≡[ runCompose ≡[ comp G F g f xs > ⟩
        apF (apF (pureF apG) (apF (apF (pureF apG) (pureF (pureG _∷_))) (apF (pureF g) (f x)))) (apF (pureF (trav GA g)) (trav FA f xs)) ≡⟨ solve F ⟩
        apF (pureF (trav GA g)) (apF (apF (pureF _∷_) (f x)) (trav FA f xs)) ∎)
          where
            FA = F .rawIA
            GA = G .rawIA
            CA = CompRawA FA GA
            open module X {a b} = RawTraversable {a = a} {b = b} ListRawTr renaming (traverse to trav)
            open RawIApplicative FA renaming (pure to pureF; ap to apF)
            open RawIApplicative GA renaming (pure to pureG; ap to apG)
            open RawIApplicative CA renaming (pure to pureC; ap to apC)
            open RawFunctor (rawATF FA) renaming (_<$>_ to mapF)
            open RawFunctor (rawATF GA) renaming (_<$>_ to mapG)
            open RawFunctor (rawATF CA) renaming (_<$>_ to mapC)

            

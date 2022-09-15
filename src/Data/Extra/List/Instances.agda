module Data.Extra.List.Instances where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Function.Base

open ≡-Reasoning

open import Data.Extra.Identity
open import Data.Extra.Compose
open import Data.Extra.Compose.Instances
open import Applicatives
open import Traversables
open import Cong-Skeletons
open import Extensionality


ListRawTr : ∀ {a b} → RawTraversable {a} {b} List
traverse ListRawTr A f []       = pure A []
traverse ListRawTr A f (x ∷ xs) = ap A (fmap (rawATF A) _∷_ (f x)) (traverse ListRawTr A f xs)

ListTr : ∀ {a} → Traversable {a} List
ListTr = record {
  rawT = ListRawTr ;
  t-nat = nat ;
  
  t-ident = ident ;

  t-comp = comp }
    where
      nat : ∀ {a} {b} {A B : Set a} {F' G' : Set a → Set b} (t : AppTrans' F' G') (f : A → F' B)
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
      comp {B = B} {A = A} {F' = F'} G F g f (x ∷ xs) = cong compose (begin 
        apF (apF (pureF apG) (apF (apF (pureF apG) (pureF (pureG _∷_))) (apF (pureF g) (f x)))) (runCompose (trav CA (λ y → compose (apF (pureF g) (f y))) xs)) ≡⟨⟩
        apF (apF (pureF apG) (apF (apF (pureF apG) (pureF (pureG _∷_))) (apF (pureF g) (f x)))) ≡[ runCompose ≡[ comp G F g f xs > ⟩
        apF ≡[ apF (pureF apG) ≡[ apF ≡[ hom F apG (pureG _∷_) ] (apF (pureF g) (f x)) > ] (apF (pureF (trav GA g)) (trav FA f xs)) ⟩
        apF ≡[ comp-hom F _ _ _ ] (apF (pureF (trav GA g)) (trav FA f xs)) ⟩
        --apF (apF (apF (apF (pureF _∘′_) (pureF apG)) (pureF (apG (pureG _∷_)))) (apF (pureF g) (f x))) (apF (pureF (trav GA g)) (trav FA f xs)) ≡⟨⟩
        --apF ≡[ apF ≡[ apF ≡[ hom F _∘′_ apG ] (pureF (apG (pureG _∷_))) ] (apF (pureF g) (f x)) ] (apF (pureF (trav GA g)) (trav FA f xs)) ⟩
        --apF ≡[ apF ≡[ hom F (_∘′_ apG) (apG (pureG _∷_)) ] (apF (pureF g) (f x)) ] (apF (pureF (trav GA g)) (trav FA f xs)) ⟩
        apF (apF (pureF (apG ∘′ apG (pureG _∷_))) (apF (pureF g) (f x))) (apF (pureF (trav GA g)) (trav FA f xs)) ≡⟨ sym (a-comp F (apF (pureF (apG ∘′ apG (pureG _∷_))) (apF (pureF g) (f x))) (pureF (trav GA g)) (trav FA f xs)) ⟩
        apF (apF (apF (pureF _∘′_) (apF (pureF (apG ∘′ apG (pureG _∷_))) (apF (pureF g) (f x)))) (pureF (trav GA g))) (trav FA f xs) ≡⟨⟩
        apF ≡[ apF ≡[ comp-hom F _ _ _ ] (pureF (trav GA g)) ] (trav FA f xs) ⟩
        --apF ≡[ apF ≡[ apF ≡[ apF ≡[ hom F _ _ ] _ ] _ ] (pureF (trav GA g)) ] (trav FA f xs) ⟩
        --apF ≡[ apF ≡[ apF ≡[ hom F _ _ ] _ ] (pureF (trav GA g)) ] (trav FA f xs) ⟩
        apF (apF (apF (pureF (_∘′_ ∘′ apG ∘′ apG (pureG _∷_))) (apF (pureF g) (f x))) (pureF (trav GA g))) (trav FA f xs) ≡⟨⟩
        apF ≡[ apF ≡[ comp-hom F _ _ _ ] (pureF (trav GA g)) ] (trav FA f xs) ⟩
        --apF ≡[ apF ≡[ apF ≡[ apF ≡[ hom F _ _ ] _ ] _ ] (pureF (trav GA g)) ] (trav FA f xs) ⟩
        --apF ≡[ apF ≡[ apF ≡[ hom F _ _ ] _ ] (pureF (trav GA g)) ] (trav FA f xs) ⟩
        apF ≡[ inter F _ _ ] (trav FA f xs) ⟩
        apF ≡[ sym (a-comp F _ _ _) ] (trav FA f xs) ⟩
        apF (apF (apF (apF (pureF _∘′_) (pureF (_$′ trav GA g))) (pureF ((_∘′_ ∘′ apG ∘′ apG (pureG _∷_)) ∘′ g))) (f x)) (trav FA f xs) ≡⟨⟩
        _ ≡⟨ lemma x xs ⟩
        apF (apF (apF (pureF (_$′ trav GA g)) (pureF _∘′_)) (apF (pureF _∷_) (f x))) (trav FA f xs) ≡⟨⟩
        apF ≡[ apF ≡[ sym (inter F _ _) ] (apF (pureF _∷_) (f x)) ] (trav FA f xs) ⟩
        apF _ (trav FA f xs) ≡⟨⟩
        apF (apF (apF (pureF _∘′_) (pureF (trav GA g))) (apF (pureF _∷_) (f x))) (trav FA f xs) ≡⟨ a-comp F _ _ _ ⟩
        apF (pureF (trav GA g)) (apF (apF (pureF _∷_) (f x)) (trav FA f xs)) ∎)
          where
            comp-hom : ∀ {a b p} {I : Set p} {H' : HIFun I a b} {i j : I} {A B C : Set a} → (H : IApplicative H') → (u : B → A) (v : C → B) (w : H' i j C)
                     → ap (H .rawIA) (pure (H .rawIA) u) (ap (H .rawIA) (pure (H .rawIA) v) w) ≡ ap (H .rawIA) (pure (H .rawIA) (u ∘′ v)) w
            comp-hom H u v w = trans (sym (a-comp H _ _ _)) (trans (cong (λ s → ap (H .rawIA) (ap (H .rawIA) s (pure (H .rawIA) v)) w) (hom H _ _)) (cong (λ s → ap (H .rawIA) s w) (hom H _ _)))


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

            
            lemma : (x : A) (xs : List A) →
                    ap FA 
                       (ap FA
                           (ap FA
                               (ap FA (pure FA _∘′_) (pure FA (_$′ traverse ListRawTr GA g)))
                               (pure FA ((_∘′_ ∘′ ap GA ∘′ ap GA (pure GA _∷_)) ∘′ g)))
                           (f x))
                       (trav FA f xs) ≡
                    ap FA
                        (ap FA
                           (ap FA (pure FA (_$′ traverse ListRawTr GA g)) (pure FA _∘′_))
                           (ap FA (pure FA _∷_) (f x)))
                        (trav FA f xs)
            lemma x [] = begin
              apF _ ≡[ refl ⟩
              apF _ (pureF []) ≡⟨ inter F _ _ ⟩
              apF _ _ ≡⟨ sym (a-comp F _ _ _) ⟩
              apF ≡[ apF ≡[ hom F _ _ ] _ ] _ ⟩
              apF ≡[ apF (pureF _) ≡[ apF ≡[ hom F _ _ ] (pureF _) > ] _ ⟩
              apF ≡[ comp-hom F _ _ _ ] _ ⟩
              apF ≡[ hom F _ _ ] _ ⟩
              sym (begin
              apF _ ≡[ refl ⟩
              apF _ (pureF []) ≡⟨ inter F _ _ ⟩
              apF _ _ ≡⟨ sym (a-comp F _ _ _) ⟩
              apF ≡[ apF ≡[ hom F _ _ ] _ ] _ ⟩
              apF ≡[ apF (pureF _) ≡[ hom F _ _ > ] _ ⟩
              apF ≡[ hom F _ _ ] _ ⟩
              _ ≡⟨ comp-hom F _ _ _ ⟩
              apF ≡[ pureF ≡[ f-ext (λ x → refl) > ] _ ⟩
              _ ∎
              )
            lemma x (y ∷ xs) = {!!} -- yeah just writing the applicative simplifier is easier...

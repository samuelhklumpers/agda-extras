{-# OPTIONS --guardedness --cubical #-}

module Data.Extra.Stream.Instances where

open import Codata.Guarded.Stream as S
open import Effect.Functor
open import Function.Base using (_∘′_; const; id; _$′_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat.Base
open import Function.Inverse hiding (sym; id)
open import Relation.Binary.PropositionalEquality

open import Cubical.Data.Equality

open import Effect.Extra.Functors
open import Effect.Extra.Applicatives
open import Effect.Extra.Monads hiding (bind)
open import Effect.Extra.Representables
-- open import Effect.Extra.Traversables


private
  variable
    a b c : Level
    A : Set a
    B : Set b


StreamRawF : RawFunctor {ℓ = a} Stream
StreamRawF = record
  { _<$>_ = S.map
  }

StreamF : Functor {a = a} Stream
StreamF = record
  { rawF = StreamRawF
  ; f-ident = λ x → pathToEq (ident x)
  ; f-comp = λ g f x → pathToEq (comp' g f x)
  }
  where
  ident : {A : Set a} → (x : Stream A) → Path (Stream A) (S.map id x) x
  head (ident x i) = head x
  tail (ident x i) = ident (tail x) i

  comp' : {A : Type a} {B : Set b} {C : Set c} → (g : B → C) (f : A → B) (x : Stream A)
         → Path (Stream C) (S.map g (S.map f x)) (S.map (g ∘′ f) x)
  head (comp' g f x i) = g (f (head x))
  tail (comp' g f x i) = comp' g f (tail x) i

map-tail-inter : {A B : Set a} → (f : A → B) → (xs : Stream (Stream A)) → Path (Stream (Stream B)) (S.map tail (S.map (S.map f) xs)) (S.map (S.map f) (S.map tail xs))
map-tail-inter f xs = compPath (eqToPath (f-comp StreamF tail (S.map f) xs)) (symPath (eqToPath (f-comp StreamF (S.map f) tail xs)))

StreamRawA : RawApplicative {a = a} Stream
StreamRawA = record
  { pure = repeat
  ; ap = S.ap }

StreamA : Applicative {a = a} Stream
StreamA = record
  { rawIA = StreamRawA
  ; a-ident = λ v → pathToEq (ident v)
  ; a-comp = λ u v w → pathToEq (comp' u v w)
  ; hom = λ f x → pathToEq (hom' f x) ;
  inter = λ u y → pathToEq (inter' u y) }
  where
  ident : ∀ {a} {A : Set a} → (v : Stream A) → Path (Stream A) (S.ap (repeat id) v) v
  head (ident v i) = head v
  tail (ident v i) = ident (tail v) i

  comp' : ∀ {a} {B C A : Type a} (u : Stream (B → C)) (v : Stream (A → B)) (w : Stream A)
          → Path (Stream C) (S.ap (S.ap (S.ap (repeat _∘′_) u) v) w) (S.ap u (S.ap v w))
  head (comp' u v w i) = head u (head v (head w))
  tail (comp' u v w i) = comp' (tail u) (tail v) (tail w) i

  hom' : ∀ {a} {A B : Type a} (f : A → B) (x : A)
         → Path (Stream B) (S.ap (repeat f) (repeat x)) (repeat (f x))
  head (hom' f x i) = f x
  tail (hom' f x i) = hom' f x i

  inter' : ∀ {a} {A B : Type a} (u : Stream (A → B)) (y : A)
           → Path (Stream B) (S.ap u (repeat y)) (S.ap (repeat (_$′ y)) u)
  head (inter' u y i) = head u y
  tail (inter' u y i) = inter' (tail u) y i

map-repeat : {A B : Set a} → (x : A) → (f : A → Stream B) → Path (Stream (Stream B)) (S.map f (repeat x)) (repeat (f x)) 
head (map-repeat x f i) = f x
tail (map-repeat x f i) = map-repeat x f i

diagonal : Stream (Stream A) → Stream A
head (diagonal xs) = head (head xs)
tail (diagonal xs) = diagonal (fmap StreamRawF tail (tail xs))

diagonal-repeatˡ : (xs : Stream A) → Path (Stream A) (diagonal (repeat xs)) xs
diagonal-repeatˡ xs = diagonal-repeat' xs (repeat xs) reflPath
  where
  diagonal-repeat' : (xs : Stream A) (ys : Stream (Stream A)) → Path (Stream (Stream A)) ys (repeat xs) → Path (Stream A) (diagonal ys) xs
  head (diagonal-repeat' xs ys p i) = head (head (p i))
  tail (diagonal-repeat' xs ys p i) = diagonal-repeat' (tail xs) (S.map tail (tail ys)) (compPath (congPath (λ ys → S.map tail (tail ys)) p) (map-repeat xs tail)) i

diagonal-repeatʳ : (xs : Stream A) → Path (Stream A) (diagonal (S.map repeat xs)) xs
diagonal-repeatʳ xs = diagonal-repeat' xs (S.map repeat xs) reflPath
  where
  diagonal-repeat' : (xs : Stream A) (ys : Stream (Stream A)) → Path (Stream (Stream A)) ys (S.map repeat xs) → Path (Stream A) (diagonal ys) xs
  head (diagonal-repeat' xs ys p i) = head (head (p i))
  tail (diagonal-repeat' xs ys p i) = diagonal-repeat' (tail xs) (S.map tail (tail ys)) (compPath (congPath (λ ys → S.map tail (tail ys)) p) (eqToPath (f-comp StreamF tail repeat (tail xs)))) i

bind : {A B : Set a} → Stream A → (A → Stream B) → Stream B
bind xs f = diagonal (fmap StreamRawF f xs)

bind-repeat : {A B : Set a} → (x : A) → (f : A → Stream B) → Path (Stream B) (bind (repeat x) f) (f x)
bind-repeat x f = compPath (congPath diagonal (map-repeat x f)) (diagonal-repeatˡ (f x))

map-diagonal : {A B : Set a} → (xss : Stream (Stream A)) → (f : A → B) → Path (Stream B) (S.map f (diagonal xss)) (diagonal (S.map (S.map f) xss))
map-diagonal xss f = map-diagonal' xss (S.map (S.map f) xss) f reflPath
  where
  map-diagonal' : {A B : Set a} → (xss : Stream (Stream A)) (yss : Stream (Stream B)) → (f : A → B) → Path (Stream (Stream B)) yss (S.map (S.map f) xss) → Path (Stream B) (S.map f (diagonal xss)) (diagonal yss)
  head (map-diagonal' xss yss f p i) = head (head (p (~ i)))
  tail (map-diagonal' xss yss f p i) = map-diagonal' (S.map tail (tail xss)) (S.map tail (tail yss)) f (compPath (congPath (λ zss → S.map tail (tail zss)) p) (map-tail-inter f (tail xss))) i

diagonal-diagonal : {A : Set a} → (xss : Stream (Stream (Stream A))) → Path (Stream A) (diagonal (diagonal xss)) (diagonal (S.map diagonal xss))
diagonal-diagonal {A = A} xss = diagonal-diagonal' xss (diagonal (diagonal (xss))) (diagonal (S.map diagonal xss)) reflPath reflPath
  where
  diagonal-diagonal' : (yss : Stream (Stream (Stream A))) (xs ys : Stream A) → Path (Stream A) xs (diagonal (diagonal yss)) → Path (Stream A) ys (diagonal (S.map diagonal yss)) → Path (Stream A) xs ys
  head (diagonal-diagonal' yss xs ys p q i) = compPath (congPath head p) (congPath head (symPath q)) i
  tail (diagonal-diagonal' yss xs ys p q i) = diagonal-diagonal' (S.map (S.map tail) (S.map tail (tail yss))) (tail xs) (tail ys) p' q' i
    where
    p' : Path (Stream A) (tail xs) (diagonal (diagonal (S.map (S.map tail) (S.map tail (tail yss)))))
    p' = compPath (congPath tail p) (congPath diagonal (map-diagonal (S.map tail (tail yss)) tail))

    q' : Path (Stream A) (tail ys) (diagonal (S.map diagonal (S.map (S.map tail) (S.map tail (tail yss)))))
    q' = compPath (congPath tail q) (symPath (compPath (congPath (λ zss → diagonal (S.map diagonal zss)) (eqToPath (f-comp StreamF (S.map tail) tail (tail yss)))) (congPath diagonal (compPath (eqToPath (f-comp StreamF diagonal (S.map tail ∘′ tail) (tail yss))) (symPath (eqToPath (f-comp StreamF tail diagonal (tail yss))))))))
    
bind-assoc :  {A B C : Set a} → (g : B → Stream C) → (f : A → Stream B) → (xs : Stream A) → Path (Stream C) (bind xs (λ x → bind (f x) g)) (bind (bind xs f) g)
bind-assoc g f xs = compPath (symPath (block-1 g f xs)) (compPath (symPath (diagonal-diagonal (block g f xs))) (block-2 g f xs))
  where
  block : {A B C : Set a} → (g : B → Stream C) → (f : A → Stream B) → (xs : Stream A) → Stream (Stream (Stream C))
  block g f xs = S.map (λ x → S.map g (f x)) xs

  block-1 : {A B C : Set a} → (g : B → Stream C) → (f : A → Stream B) → (xs : Stream A) → Path (Stream C) (diagonal (S.map diagonal (block g f xs))) (bind xs (λ x → bind (f x) g))
  block-1 g f xs = congPath diagonal (eqToPath (f-comp StreamF diagonal (λ x → S.map g (f x)) xs))

  block-2 : {A B C : Set a} → (g : B → Stream C) → (f : A → Stream B) → (xs : Stream A) → Path (Stream C) (diagonal (diagonal (block g f xs))) (bind (bind xs f) g)
  block-2 g f xs = compPath
   (congPath (λ ys → diagonal (diagonal ys)) (symPath (eqToPath (f-comp StreamF (S.map g) f xs))))
   (symPath (congPath diagonal (map-diagonal (S.map f xs) g)) )


StreamRawM : RawMonad {a = a} Stream
StreamRawM = record
  { return = repeat
  ; _>>=_ = bind }

StreamM : Monad {a = a} Stream
StreamM = record
  { rawM = StreamRawM
  ; left-id = λ x f → pathToEq (bind-repeat x f)
  ; right-id = λ m → pathToEq (diagonal-repeatʳ m)
  ; assoc = λ m f g → pathToEq (bind-assoc g f m) }

StreamRep : Representable {a = a} {c = lzero} Stream
StreamRep {a = a} = record
  { Rep = ℕ ;
    rep = inverse lookup' S.tabulate sec ret
  }
  where
    lookup' : {A : Set a} (x : Stream A) → ℕ → A
    lookup' x i = S.lookup i x

    sec : {A : Set a} (x : Stream A) → S.tabulate (lookup' x) ≡ x
    sec {A = A} x = pathToEq (sec' x)
      where
      sec' : (x : Stream A) → Path (Stream A) (S.tabulate (lookup' x)) x
      head (sec' x i) = head x
      tail (sec' x i) = sec' (tail x) i 

    ret : {A : Set a} (f : ℕ → A) → lookup' (S.tabulate f) ≡ f
    ret {A = A} f = pathToEq (λ i k → ret' f k i) -- this is f-ext
      where
      ret' : (f : ℕ → A) (k : ℕ) → Path A (lookup' (S.tabulate f) k) (f k)
      ret' f zero    i = f 0
      ret' f (suc k) i = ret' (f ∘′ suc) k i

-- TODO Traversable Stream

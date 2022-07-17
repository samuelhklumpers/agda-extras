open import Data.Unit
open import Data.List as L
open import Data.String as S
open import Effect.Monad.Indexed


module FileHandleEx where
  H : Set
  H = List String

  data Handled : H → H → Set → Set where
    openf  : ∀ {i} (fn : String) → Handled i (fn ∷ i) ⊤ -- let's not pay attention to what happens if you open the same thing twice
    closef : ∀ {i} (fn : String) → Handled (fn ∷ i) i ⊤
    ret    : ∀ {i A} (x : A) → Handled i i A

  data _∈_ {A : Set} : A → List A → Set where
    hd : ∀ {x xs}                → x ∈ (x ∷ xs)
    tl : ∀ {x y xs} {_ : x ∈ xs} → x ∈ (y ∷ xs)

  postulate
    read : ∀ {i : List String} (fn : String) (p : fn ∈ i) → Handled i i String -- let's pretend this uses a more appropriate file handle rather than fn
    bind : ∀ {i j k A B} → Handled i j A → (A → Handled j k B) → Handled i k B -- something is breaking this free monad, but I'm not sure what it is, hence postulate

  instance
    HandledRawMon : RawIMonad Handled
    HandledRawMon = record { return = ret ; _>>=_ = bind }

  open RawIMonad HandledRawMon

  good : Handled [] [] String
  good = do
    openf  "example.txt"
    text ← read "example.txt" hd -- pretend this is done by some instance argument magic
    closef "example.txt"
    return text

  {-
  bad1 : Handled [] [] String
  bad1 = do
    openf  "example.txt"
    text ← read "example.txt" hd
    return text
  -}

  {-
  bad2 : Handled [] [] String
  bad2 = do
    openf  "example.txt"
    text ← read "example.txt" hd
    closef "example.txt"
    text ← read "example.txt" {!!}
    return text
  -}

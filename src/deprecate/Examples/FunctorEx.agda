module Examples.FunctorEx where

open import Data.List as L
open import Data.Vec as V
open import Data.Nat hiding (_⊔_; suc)
open import Data.Bool
open import Level renaming (zero to lzero)

open import Effect.Extra.Functors

private
  variable
    ℓ ℓ′ : Level
    A B : Set ℓ

record X (F : Set ℓ → Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  field
    _<f>_ : (A → B) → F A → F B

open X {{...}}

mapList : (A → B) → L.List A → L.List B
mapList f []       = []
mapList f (x L.∷ xs) = f x L.∷ mapList f xs

Vec' : ℕ → Set ℓ → Set ℓ
Vec' n a = Vec a n

instance
  -- (*)
  LX : ∀ {ℓ} → RawFunctor {ℓ = ℓ} L.List
  LX = record { _<$>_ = mapList }

  --VX : ∀ {ℓ n} → RawFunctor {ℓ = ℓ} (Vec' n)
  --VX = {!!}

--ys : L.List Bool
--ys = not <$> (true L.∷ false L.∷ L.[])

--   good
xs : {{Functor {a = lzero} (Vec' 2)}} → V.Vec (L.List Bool) 2
xs = (true L.∷_) <$> ({!!} ∷ (L.[] ∷ []))

-- whether this typechecks depends on the presence of *
-- very bad
-- zs = fmap {F = {!!}} {!!} {!!}

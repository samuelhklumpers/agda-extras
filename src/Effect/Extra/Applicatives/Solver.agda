{-# OPTIONS --safe #-}

module Effect.Extra.Applicatives.Solver where

open import Data.Nat renaming (_⊔_ to _⊔ⁿ_)
open import Data.Product hiding (zip)
open import Data.Sum hiding (reduce)
open import Function.Base using (_$′_; _∘′_; id ; _on_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding (inspect; [_])


open import Effect.Extra.Applicatives
open import Misc.Cong-Reasoning

open ≡-Reasoning

open import Reflection
open import Reflection.AST.Argument
open import Reflection.AST.Term as Term
open import Reflection.AST.AlphaEquality
open import Reflection.AST.Name as Name
open import Reflection.TCM.Syntax renaming (pure to pureT)
open import Data.Nat.Reflection
open import Data.List.Reflection
import Data.Vec.Reflection as Vec
open import Data.Unit.Base using (⊤)
open import Data.Vec.Base   as Vec     using (Vec; _∷_; [])
open import Data.Maybe.Base as Maybe   using (Maybe; just; nothing; fromMaybe)
open import Data.List.Base  as List    using (List; _∷_; [])


{-
private
  VarMap : Set
  VarMap = ℕ → Maybe Term

  getVisible : Arg Term → Maybe Term
  getVisible (arg (arg-info visible _) x) = just x
  getVisible _                            = nothing

  getVisibleArgs : ∀ n → Term → Maybe (Vec Term n)
  getVisibleArgs n (def _ xs) = Maybe.map Vec.reverse
    (List.foldl f c (List.mapMaybe getVisible xs) n)
    where
    f : (∀ n → Maybe (Vec Term n)) → Term → ∀ n → Maybe (Vec Term n)
    f xs x zero    = just []
    f xs x (suc n) = Maybe.map (x ∷_) (xs n)

    c : ∀ n → Maybe (Vec Term n)
    c zero     = just []
    c (suc _ ) = nothing
  getVisibleArgs _ _ = nothing

  malformedGoalError : ∀ {a} {A : Set a} → Term → TC A
  malformedGoalError found = typeError
    ( strErr "Malformed call to solve."
    ∷ strErr "Goal type should be of the form: LHS ≈ RHS"
    ∷ strErr "Instead: "
    ∷ termErr found
    ∷ [])

  {-
  curriedTerm : NatSet → Term
  curriedTerm = List.foldr go Vec.`[] ∘ NatSet.toList
    where
    go : ℕ → Term → Term
    go x xs = var x [] Vec.`∷ xs-}
-}

private
  variable
    a b : Level


--* Intermediate datastructures
data AppRep (F : Set a → Set a) (A : Set a) : Set (lsuc a) where
  Pure : A → AppRep F A
  Raw  : F A → AppRep F A
  _◯_  : {B : Set a} → AppRep F (B → A) → AppRep F B → AppRep F A

apR : ∀ {A B} {F : Set a → Set a} → AppRep F (B → A) → AppRep F B → AppRep F A
apR = _◯_

-- FreeAL F A represents a value F A in its left associating simplified form, that is, having a single pure at the left, followed by a chain of zero or more applications like
-- ((pure f ⊛ u) ⊛ v) ⊛ ...
-- adapted from https://arxiv.org/abs/1403.0749 and https://hackage.haskell.org/package/free-5.1.9/docs/Control-Applicative-Trans-Free.html
data FreeAL (F : Set a → Set a) (A : Set a) : Set (lsuc a) where
  PureL : A → FreeAL F A
  _:*:_ : {B : Set a} → FreeAL F (B → A) → F B → FreeAL F A


--* Conversion from intermediate structure to terms
module _ {F : Set a → Set a} (F' : RawApplicative F) where
  private
    open module X = RawIApplicative F' renaming (pure to pureF; ap to apF)
    
    variable
      A B C : Set a

  evalRep : AppRep F A → F A
  evalRep (Pure x) = pureF x
  evalRep (Raw x) = x
  evalRep (r ◯ s) = apF (evalRep r) (evalRep s)

  runFreeAL : FreeAL F A → F A
  runFreeAL (PureL x) = pureF x
  runFreeAL (r :*: x) = apF (runFreeAL r) x


--* Zipping
module _ {a : Level} {F : Set a → Set a} where
  private
    variable
      A B C D : Set a

  zip-pure : (B → A) → FreeAL F B → FreeAL F A
  zip-pure f (PureL x) = PureL (f x)
  zip-pure f (u :*: v) = zip-pure (f ∘′_) u :*: v

  zip : FreeAL F (B → A) → FreeAL F B → FreeAL F A
  zip u         (v :*: w) = zip (zip-pure _∘′_ u) v :*: w
  zip (PureL f) (PureL y) = PureL (f y)
  zip (u :*: v) (PureL y) = zip-pure (_$′ y) (u :*: v)

  simplify : AppRep F A → FreeAL F A
  simplify (Pure x) = PureL x
  simplify (Raw f)  = PureL id :*: f
  simplify (u ◯ v)  = zip (simplify u) (simplify v)


--* Theorem: simplify respects equality
module _ {a : Level} {F : Set a → Set a} (F'' : Applicative F) where
  private
    F' = F'' .rawIA
    
    open module X = RawIApplicative F' renaming (pure to pureF; ap to apF)
    
    variable
      A B C : Set a

  zip-pure-≈ : (f : B → A) → (u : FreeAL F B) → runFreeAL F' (zip-pure f u) ≡ apF (pureF f) (runFreeAL F' u)
  zip-pure-≈ f (PureL x) = sym (hom F'' _ _)
  zip-pure-≈ f (u :*: v) = begin
    apF ≡[ zip-pure-≈ (f ∘′_) u ] v ⟩
    apF ≡[ apF ≡[ sym (hom F'' _∘′_ f) ] (runFreeAL F' u) ] v ⟩
    apF (apF (apF (pureF _∘′_) (pureF f)) (runFreeAL F' u)) v ≡⟨ a-comp F'' _ _ _ ⟩
    apF (pureF f) (apF (runFreeAL F' u) v) ∎

  zip-≈ : (u : FreeAL F (B → A)) → (v : FreeAL F B) → runFreeAL F' (zip u v) ≡ apF (runFreeAL F' u) (runFreeAL F' v)
  zip-≈ u         (v :*: w) = begin
    apF ≡[ zip-≈ (zip-pure _∘′_ u) v ] w ⟩
    apF ≡[ apF ≡[ zip-pure-≈ _∘′_ u ] (runFreeAL F' v) ] w ⟩
    apF (apF (apF (pureF _∘′_) (runFreeAL F' u)) (runFreeAL F' v)) w ≡⟨ a-comp F'' _ _ _ ⟩
    apF (runFreeAL F' u) (runFreeAL F' (v :*: w)) ∎
  zip-≈ (PureL f) (PureL y) = sym (hom F'' _ _)
  zip-≈ (u :*: v) (PureL y) = trans (zip-pure-≈ (_$′ y) (u :*: v)) (sym (inter F'' _ _))
  
  simplify-≈ : (u : AppRep F A) → runFreeAL F' (simplify u) ≡ evalRep F' u
  simplify-≈ (Pure x) = refl
  simplify-≈ (Raw f)  = a-ident F'' f 
  simplify-≈ (u ◯ v)  = trans (zip-≈ (simplify u) (simplify v)) (cong₂ apF (simplify-≈ u) (simplify-≈ v))

  {-
  simplify-solution : Term → Term → TC Term
  simplify-solution `app `lhs = {!!}

  simplify-macro : Name → Term → TC ⊤
  simplify-macro applicative hole = do
    hole′ ← inferType hole >>= reduce
    just (lhs ∷ rhs ∷ []) ← pureT (getVisibleArgs 2 hole′)
      where nothing → malformedGoalError hole′
    {!!}
  -}

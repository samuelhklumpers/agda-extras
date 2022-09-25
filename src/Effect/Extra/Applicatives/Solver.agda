{-# OPTIONS --safe --experimental-lossy-unification #-}

module Effect.Extra.Applicatives.Solver where

open import Data.Sum.Base hiding (reduce)
open import Function.Base using (_$′_; _∘′_; id ; _on_)
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality.Core

open import Effect.Extra.Applicatives
open import Misc.Cong-Reasoning

open ≡-Reasoning

open import Reflection
open import Reflection.AST.Argument
open import Reflection.AST.Term as Term
open import Reflection.AST.Name as Name
open import Reflection.TCM.Syntax renaming (pure to pureT)
open import Data.List.Reflection
import Data.Vec.Reflection as Vec
open import Data.Unit.Base using (⊤)
open import Data.Nat.Base
open import Data.Vec.Base   as Vec     using (Vec; _∷_; [])
open import Data.Maybe.Base as Maybe   using (Maybe; just; nothing; fromMaybe)
open import Data.List.Base  as List    using (List; _∷_; [])


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

  simplify' : AppRep F A → FreeAL F A
  simplify' (Pure x) = PureL x
  simplify' (Raw f)  = PureL id :*: f
  simplify' (u ◯ v)  = zip (simplify' u) (simplify' v)


--* Theorem: simplify' respects equality
module SimplifyTheorem {a : Level} {F : Set a → Set a} (F'' : Applicative F) where
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

  simplify-≈ : (u : AppRep F A) → evalRep F' u ≡ runFreeAL F' (simplify' u)
  simplify-≈ (Pure x) = refl
  simplify-≈ (Raw f)  = sym (a-ident F'' f) 
  simplify-≈ (u ◯ v)  = trans (cong₂ apF (simplify-≈ u) (simplify-≈ v)) (sym (zip-≈ (simplify' u) (simplify' v)))


open SimplifyTheorem public


--* Macros
-- largely adapted from https://agda.github.io/agda-stdlib/Tactic.RingSolver.html

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
  ( strErr "Malformed call to solve. "
  ∷ strErr "Goal type should be of the form: LHS ≈ RHS "
  ∷ strErr "Instead: "
  ∷ termErr found
  ∷ [])

{-
curriedTerm : NatSet → Term
curriedTerm = List.foldr go Vec.`[] ∘ NatSet.toList
  where
  go : ℕ → Term → Term
  go x xs = var x [] Vec.`∷ xs
-}

convertTerm : Term → Term → TC Term
convertTerm `app = convert
  where
  `raw = def (quote rawIA) (`app ⟨∷⟩ [])

  mutual
    convert : Term → TC Term
    convert (def (quote ap)   xs) = convertOp₂ (quote _◯_)  xs
    convert (def (quote pure) xs) = convertOp₁ (quote Pure) xs
    convert t = return (con (quote Raw) (t ⟨∷⟩ []))

    convertOp₂ : Name → Args Term → TC Term
    convertOp₂ nm (x ⟨∷⟩ y ⟨∷⟩ []) = do
      x' ← convert x
      y' ← convert y
      return (con nm (x' ⟨∷⟩ y' ⟨∷⟩ []))
    convertOp₂ nm (x ∷ xs)         = convertOp₂ nm xs
    convertOp₂ _  _                = return unknown

    convertOp₁ : Name → Args Term → TC Term
    convertOp₁ nm (x ⟨∷⟩ []) = do
      return (con nm (x ⟨∷⟩ []))
    convertOp₁ nm (x ∷ xs)   = convertOp₁ nm xs
    convertOp₁ _  _          = return unknown

    {-
    convertUnknownName : Name → Args Term → TC Term
    convertUnknownName nm xs = do
      nameTerm ← normalise (def nm [])
      if (nameTerm =α= add) then convertOp₂ (quote _⊕_) xs else
        if (nameTerm =α= mul) then convertOp₂ (quote _⊗_) xs else
          if (nameTerm =α= neg) then convertOp₁ (quote ⊝_)  xs else
            if (nameTerm =α= pow) then convertExp             xs else
              if (nameTerm =α= sub) then convertSub            xs else
                return (`Κ (def nm xs))

    convertSuc : Term → TC Term
    convertSuc x = do x' ← convert x; return (quote _⊕_ $ᵉ (`Κ (toTerm 1) ⟨∷⟩ x' ⟨∷⟩ []))
    -}

`sym : Term → Term
`sym x≡y = def (quote sym) (x≡y ⟨∷⟩ [])

`trans : Term → Term → Term
`trans x≡y y≡z = def (quote trans) (x≡y ⟨∷⟩ y≡z ⟨∷⟩ [])

`correct : Term → Term → Term
`correct `app `rep = def (quote simplify-≈) (`app ⟨∷⟩ `rep ⟨∷⟩ [])

simplify-solution : Term → Term → TC Term
simplify-solution `app `lhs = do
  `lhsRep ← convertTerm `app `lhs

  debugPrint "simplify-solution" 2 (strErr "original term " ∷ termErr `lhs ∷ [])
  debugPrint "simplify-solution" 2 (strErr "term representation " ∷ termErr `lhsRep ∷ [])
 
  return (`correct `app `lhsRep)

solve-solution : Term → Term → Term → TC Term
solve-solution `app `lhs `rhs = do
  `lhsRep ← convertTerm `app `lhs
  `rhsRep ← convertTerm `app `rhs

  debugPrint "solve-solution" 2 (strErr "original lhs " ∷ termErr `lhs ∷ [])
  debugPrint "solve-solution" 2 (strErr "lhs representation " ∷ termErr `lhsRep ∷ [])

  debugPrint "solve-solution" 2 (strErr "original rhs " ∷ termErr `rhs ∷ [])
  debugPrint "solve-solution" 2 (strErr "rhs representation " ∷ termErr `rhsRep ∷ [])

  return (`trans (`correct `app `lhsRep) (`sym (`correct `app `rhsRep)))


`Applicative : Term
`Applicative = def (quote Applicative) (1 ⋯⟨∷⟩ [])

checkIsApplicative : Term → TC Term
checkIsApplicative applicative = checkType applicative `Applicative

simplify-macro : Term → Term → TC ⊤
simplify-macro applicative hole = do
  `app ← checkIsApplicative applicative
  hole′ ← inferType hole >>= normalise
  just (lhs ∷ rhs ∷ []) ← pureT (getVisibleArgs 2 hole′)
    where nothing → malformedGoalError hole′

  solution ← simplify-solution `app lhs
  unify hole solution

solve-macro : Term → Term → TC ⊤
solve-macro applicative hole = do
  `app ← checkIsApplicative applicative
  hole′ ← inferType hole >>= normalise
  just (lhs ∷ rhs ∷ []) ← pureT (getVisibleArgs 2 hole′)
    where nothing → malformedGoalError hole′

  solution ← solve-solution `app lhs rhs
  unify hole solution

macro
  simplify : Term → Term → TC ⊤
  simplify = simplify-macro

  solve : Term → Term → TC ⊤
  solve = solve-macro

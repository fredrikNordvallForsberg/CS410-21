module Lectures.Hutton where

open import Data.Nat hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Maybe hiding (decToMaybe)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

---------------------------------------------------------------------------
-- Expressions
---------------------------------------------------------------------------

data Expr : Set where
  num : ℕ -> Expr
  bit : Bool -> Expr
  _+E_ : Expr -> Expr -> Expr
  ifE_then_else_ : Expr -> Expr -> Expr -> Expr



e1 : Expr
e1 = num 7 +E num 3 +E num 5

e2 : Expr
e2 = (ifE bit true then num 0 +E num 2 else num 4 +E num 0 +E num 0) +E num 0

ne3 : Expr
ne3 = ifE num 6 then bit false else bit true

---------------
-- Evaluation
---------------

data Val : Set where
  num : ℕ -> Val
  bit : Bool -> Val

_+V_ : Val -> Val -> Maybe Val
num x +V num y = just (num (x + y))
_ +V _ = nothing

eval : Expr -> Maybe Val
eval (num n) = just (num n)
eval (bit b) = just (bit b)
eval (e +E e') = do
  v ← eval e
  v' ← eval e'
  v +V v'
eval (ifE e then e' else e'') = do
  (bit b) ← eval e where _ → nothing
  if b then eval e' else eval e''

_ : eval e1 ≡ just (num 15)
_ = refl

_ : eval e2 ≡ just (num 2)
_ = refl

_ : eval ne3 ≡ nothing
_ = refl

---------------
-- Summary
---------------

-- * Use 'data' to represent expressions
-- * Use pattern matching to evaluate them
-- * So far, this could all have been done in Haskell
--   (but we have nicer syntax for pattern matching in a do block)
-- * The use of Maybe makes life harder


---------------------------------------------------------------------------
-- Typed expressions
---------------------------------------------------------------------------

data Ty : Set where
  nat : Ty
  bool : Ty

data TExpr : Ty -> Set where
  num : ℕ -> TExpr nat
  bit : Bool -> TExpr bool
  _+E_ : TExpr nat -> TExpr nat -> TExpr nat
  ifE_then_else_ : ∀ {t} → TExpr bool -> TExpr t -> TExpr t -> TExpr t

te1 : TExpr nat
te1 = num 7 +E num 3 +E num 5

te2 : TExpr nat
te2 = (ifE bit true then num 0 +E num 2 else num 4 +E num 0 +E num 0) +E num 0

-- tne3 : TExpr ?
-- tne3 = ifE num 6 then bit false else bit true

---------------
-- Evaluation
---------------

TVal : Ty -> Set
TVal nat = ℕ
TVal bool = Bool

teval : ∀ {t} → TExpr t -> TVal t
teval (num n) = n
teval (bit b) = b
teval (e +E e') = teval e + teval e'
teval (ifE e then e' else e'') = if teval e then teval e' else teval e''

_ : teval te1 ≡ 15
_ = refl

_ : teval te2 ≡ 2
_ = refl

---------------
-- Summary
---------------

-- * Use indexed 'data' to represent typed expressions
-- * Use pattern matching to evaluate them
-- * No need for Maybe anymore, as expressions don't go wrong by construction


---------------------------------------------------------------------------
-- Relating typed and untyped expressions
---------------------------------------------------------------------------

∣_∣  : ∀ {t} → TExpr t -> Expr
∣ num n ∣ = num n
∣ bit b ∣ = bit b
∣ e +E e' ∣ = ∣ e ∣ +E ∣ e' ∣
∣ ifE e then e' else e'' ∣ = ifE ∣ e ∣ then ∣ e' ∣ else ∣ e'' ∣


record Welltyped (e : Expr) : Set where
  constructor okay
  field
    τ : Ty
    t : TExpr τ
    is-same : ∣ t ∣ ≡ e


_≟'_ : (τ : Ty) -> (τ' : Ty) -> Dec (τ ≡ τ')
nat ≟' nat = yes refl
nat ≟' bool = no (λ ())
bool ≟' nat = no (λ ())
bool ≟' bool = yes refl

decToMaybe : {P : Set} -> Dec P -> Maybe P
decToMaybe (yes p) = just p
decToMaybe (no p)  = nothing

_≟_ : (τ : Ty) -> (τ' : Ty) -> Maybe (τ ≡ τ')
x ≟ y = decToMaybe (x ≟' y)

infer : (e : Expr) -> Maybe (Welltyped e)
infer (num n) = just (okay nat (num n) refl)
infer (bit b) = just (okay bool (bit b) refl)
infer (e +E e') = do
  okay nat t p ← infer e where _ → nothing
  okay nat t' p' ← infer e' where _ → nothing
  just (okay nat (t +E t') (cong₂ _+E_ p p'))
infer (ifE e then e' else e'') = do
  okay bool t refl ← infer e where _ → nothing
  okay τ t' refl ← infer e'
  okay τ' t'' refl ← infer e''
  refl <- τ ≟ τ'
  just (okay τ (ifE t then t' else t'') refl)

∣_∣V : ∀ {t} → TVal t -> Val
∣_∣V {nat} = num
∣_∣V {bool} = bit

eval' : Expr -> Maybe Val
eval' e = do
  okay _ t _ ← infer e
  just ∣ teval t ∣V

_ : eval' e1 ≡ just (num 15)
_ = refl

_ : eval' e2 ≡ just (num 2)
_ = refl

_ : eval' ne3 ≡ nothing
_ = refl

---------------
-- Summary
---------------

-- * There is an obvious way to go from more information to less information
-- * For well-formed expressions, we can go the other way
-- * Can factor unsafe evaluation unsafe infer + safe eval
--   (should be slightly more efficient)
















---------------
-- Fixeties
---------------

infixl 4 _+E_
infix 0 ifE_then_else_

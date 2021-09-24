module NowYouTry.PredicateLogic where

open import Data.Nat -- ℕ \bN

open import Data.Unit
open import Data.Empty
open import Data.Product hiding (curry; uncurry)
open import Data.Sum
open import Relation.Nullary

-- Propositional logic: A and B implies C
-- Predicate logic:     (isMan(x) implies isMortal(x)) and isMan(Socrates)

----------------------------------------------------------------------
-- Predicates in type theory
----------------------------------------------------------------------

-- What is a predicate (on natural numbers, say)?

Pred : Set -> Set1
Pred A = A -> Set

isEven : ℕ -> Set
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc n)) = isEven n


-- 4 = suc (suc 2)
-- 2 = suc (suc 0)
test : isEven 4 -- = isEven 2 = isEven 0 = ⊤
test = tt

test' : ¬ isEven 5
test' ()

_>1 : ℕ -> Set
zero >1 = ⊥
suc zero >1 = ⊥
suc (suc n) >1 = ⊤

_<3 : ℕ -> Set
zero <3 = ⊤
suc zero <3 = ⊤
suc (suc zero) <3 = ⊤
suc (suc (suc n)) <3 = ⊥

fact : 1 <3 × 2 >1
fact = _




----------------------------------------------------------------------
-- Quantifiers (∀, ∃)
----------------------------------------------------------------------

-------------------------------
-- Universal quantification ∀
-------------------------------

-- Q: What is a proof of (∀ x : A) P(x)?

-- A: A method which produces a proof of P(a) for any given a : A -- a dependent function!





∀' : (A : Set) -> (P : A -> Set) -> Set
∀' A P = (x : A) -> P x

ex8 : (n : ℕ) -> isEven n ⊎ isEven (suc n)
ex8 zero = inj₁ tt
ex8 (suc zero) = inj₂ tt
ex8 (suc (suc n)) = ex8 n

-- Note: `A → B` is "just" (_ : A) -> B

---------------------------------
-- Existential quantification ∃
---------------------------------

-- Q: What is a proof of (∃ x : A) P(x)?

-- A: A choice of a : A, and a proof of P(a) -- a dependent tuple

∃' : (A : Set) -> (P : A -> Set) -> Set
∃' A P = Σ[ x ∈ A ] (P x)

ex9 : Σ ℕ isEven
ex9 = 4 , tt

-- ((∃ x : A) P(x)) → Q implies
-- (∀ x : A) (P(x) → Q) and vice versa

curry : {A : Set}{P : A -> Set}{Q : Set} ->
        ((Σ[ x ∈ A ] (P x)) -> Q) -> ((x : A) -> (P x -> Q))
curry f a p = f (a , p)

uncurry : {A : Set}{P : A -> Set}{Q : Set} ->
          ((x : A) -> (P x -> Q)) -> ((Σ[ x ∈ A ] (P x)) -> Q)
uncurry g (a , p) = g a p


-- Note: A × B is "just" Σ[ _ ∈ A ] B



-- Now you try

theoremofChoice : {A B : Set}{R : A -> B -> Set} ->
                  ((a : A) -> Σ[ b ∈ B ] (R a b)) ->
                  (Σ[ f ∈ (A -> B) ] ((a : A) -> R a (f a)))
theoremofChoice p = {!!}

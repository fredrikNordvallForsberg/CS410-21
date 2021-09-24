module Lectures.Logic where

{-

Traditional programming languages:

---------------------        ---------------------
|                   |        |                   |
|      Program      |        |   Specification   |
|                   |        |                   |
---------------------        ---------------------
    In computer                    On paper

-}

{-

Dependently types programming languages:

   ---------------------------------------
   |                                     |
   |      Program   :    Specification   |
   |                                     |
   ---------------------------------------
                   In computer

-}


{-

For this to work, we need to represent specifications = logical formulue
in our language.

-}

----------------------------------------------------------------------
-- Propositions-as-booleans?
----------------------------------------------------------------------

{-

First thought: use Bool, ie say that a proposition is either true or false.

-}

data Bool : Set where -- can be found in Data.Bool
  false true : Bool

-- We can define eg `and` by pattern matching:

_&_ : Bool -> Bool -> Bool
false & y = false
true & y = y

-- but how do we represent eg `(∀ n : ℕ) P(n)`?

-- Problem: with Propositions = Bool, we can only represent decidable
-- properties.

----------------------------------------------------------------------
-- Propositions-as-types
----------------------------------------------------------------------

-- What is a proposition? Something which might have a proof

-- Leap: identify a proposition with its "set" of proofs, ie

Proposition = Set

--          PROOFS = PROGRAMS

----------------
-- Implication
----------------

-- Q: What is a proof of `A → B`?

-- A: A method for converting proofs of A into proofs of B -- a function!

_⇒_ : Set -> Set -> Set
A ⇒ B = A -> B

I : {A : Set} -> A -> A
I a = a


ex1 : {A B C D : Set} -> ((A -> B -> C) -> D) -> (A -> C) -> D
ex1 f g = f (λ a b → g a)

----------------
-- Conjunction
----------------

-- Q: What is a proof of `A ∧ B`?

-- A: A proof of A and a proof of B -- a tuple!

open import Data.Product -- _×_ \times

_∧_ : Set -> Set -> Set
A ∧ B = A × B

ex2 : {A B : Set} -> A × B -> A
ex2 = proj₁

ex3 : {A : Set} -> A -> A × A
ex3 a = (a , a)

----------------
-- True and False
----------------

-- the unit type represents a true proposition

open import Data.Unit -- ⊤ \top

ex4 : {B : Set} -> B -> ⊤
ex4 b = _

test = ex4 {⊤ -> ⊤} (λ x -> x)

-- the empty type represents a false proposition

open import Data.Empty -- ⊥ \bot

ex5 : {B : Set} -> ⊥ -> B
ex5 ()

----------------
-- Disjunction
---------------

-- Q: What is a proof of `A ∨ B`?

-- A: A proof of A, or a proof of B -- a disjoint union

open import Data.Sum -- _⊎_ \uplus

_∨_ : Set -> Set -> Set
A ∨ B = A ⊎ B

ex6 : {A B : Set} -> A ⊎ B -> B ⊎ A
ex6 (inj₁ a) = inj₂ a -- ₂ \_2
ex6 (inj₂ b) = inj₁ b -- ₁ \_1

----------------
-- Negation
----------------

-- Q: What is a proof of `¬ A`?

-- A: A method to show that all proofs of A are impossible -- a function A → ⊥

¬_ : Set -> Set
¬ A = A -> ⊥

ex7 : ¬ (⊤ -> ⊥)
ex7 x = x tt

explosion : {A B : Set} -> A -> ¬ A -> B
explosion a ¬a = ex5 (¬a a)









{-
-- Now you try:

materialImplication : {A B : Set} -> (¬ A ⊎ B) -> (A -> B)
materialImplication = {!!}
-}

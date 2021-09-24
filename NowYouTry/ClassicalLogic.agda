module NowYouTry.ClassicalLogic where

open import Data.Sum
open import Data.Empty
open import Relation.Nullary

-- the law of excluded middle

LEM : Set1
LEM = {P : Set} -> P ⊎ ¬ P

{-
lem : LEM -- not provable
lem {P} = {!!}
-}

-- double negation elimination

DNE : Set1
DNE = {P : Set} -> ¬ ¬ P -> P

{-
dne : DNE -- not provable
dne {P} ¬¬p = {!!}
-}

-- these are classical principles

LEM→DNE : LEM -> DNE
LEM→DNE lem {P} ¬¬p with lem {P}
LEM→DNE lem {P} ¬¬p | inj₁ p = p
LEM→DNE lem {P} ¬¬p | inj₂ ¬p = ⊥-elim (¬¬p ¬p)

-- Now you try

DNE→LEM : DNE -> LEM
DNE→LEM dne {P} = {!!}
-- hint: you probably want to make your first move `dne`


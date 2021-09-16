module NowYouTry.BeingPrecise where

open import Agda.Builtin.Nat

data List (A : Set) : Set where
  [] : List A
  _∷_ : A -> List A -> List A

{-
_!!_ : ∀ {A} → List A -> Nat -> A
[] !! n = {!!}
(x ∷ xs) !! zero = x
(x ∷ xs) !! suc n = xs !! n
-}

{-
open import Data.Maybe

_!!_ : ∀ {A} → List A -> Nat -> Maybe A
[] !! n = nothing
(x ∷ xs) !! zero = just x
(x ∷ xs) !! suc n = xs !! n
-}

data Vec (A : Set) : Nat -> Set where
  [] : Vec A 0
  _∷_ : ∀ {n} → A -> Vec A n -> Vec A (suc n)

data Fin : Nat -> Set where
  zero : ∀ {n} → Fin (suc n)
  suc : ∀ {n} → Fin n -> Fin (suc n)

_!!_ : ∀ {A n} → Vec A n -> Fin n -> A
(x ∷ xs) !! zero = x
(x ∷ xs) !! suc n = xs !! n

-- now you try:
--  convert the Haskell head and tail functions from lists to vectors

head : ∀ {A} → List A -> A
head = {!!}

tail : ∀ {A} → List A -> List A
tail = {!!}

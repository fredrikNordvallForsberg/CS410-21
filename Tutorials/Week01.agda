module Tutorials.Week01 where

open import Data.Unit
open import Relation.Nullary

-- Don't worry about not having all tools for Coursework 1 yet





-- Fin, Nat

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

toℕ : ∀ {n} → Fin n → ℕ
toℕ Fin.zero = ℕ.zero
toℕ (suc x) = suc (toℕ x)

fromℕ : (n : _) → Fin (suc n)
fromℕ ℕ.zero = Fin.zero
fromℕ (suc n) = suc (fromℕ n)


-- constructor overloading
-- Implicit arguments, forall, unification

-- could lookup be as precise in Haskell as in Agda?

-- "How U and x works and how to use them"?



-- Disjoint union

data _⊎_ (A B : Set) : Set where -- \uplus
  inj₁ : A -> A ⊎ B
  inj₂ : B -> A ⊎ B

-- iFits?

fromℕ' : ∀ {m} → ℕ → Fin m ⊎ ⊤
fromℕ' {zero} x = inj₂ tt
fromℕ' {suc m} zero = inj₁ zero
fromℕ' {suc m'} (suc x) with fromℕ' {m'} x
... | inj₁ y = inj₁ (Fin.suc y)
... | inj₂ tt = inj₂ tt





-- Records

record BoundedNat : Set where
  field
    bound : ℕ
    num : Fin bound
open BoundedNat

forget : BoundedNat → ℕ
forget x = toℕ (num x)

raise : ∀ {n} → Fin n → Fin (suc n)
raise zero = zero
raise (suc x) = suc (raise x)

incBound : BoundedNat → BoundedNat
bound (incBound x) = suc (suc (bound x))
num (incBound x) = raise (raise (num x))

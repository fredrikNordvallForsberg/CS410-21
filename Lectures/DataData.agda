module Lectures.DataData where

import Level as L
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Container hiding (refl)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

---------------------------------------------------------------------------
-- Describing data types
---------------------------------------------------------------------------
{-
data ℕ : Set where
  zero : ℕ
  suc : ℕ -> ℕ

pred : ℕ -> ℕ
pred zero = zero
pred (suc n) = n
-}

{-
data ℕ : Set where
  zeroOrSuc : (b : Bool) -> if b then ⊤ else ℕ -> ℕ

-- zero : ℕ
pattern zero = zeroOrSuc true tt

-- suc : ℕ -> ℕ
pattern suc n = zeroOrSuc false n

pred : ℕ -> ℕ
pred zero = zero
pred (suc n) = n
-}

{-
data ℕ : Set where
  zeroOrSuc : Σ[ b ∈ Bool ] (if b then ⊤ else ℕ) -> ℕ

pattern zero = zeroOrSuc (true , tt)
pattern suc n = zeroOrSuc (false , n)

pred : ℕ -> ℕ
pred zero = zero
pred (suc n) = n
-}

ArgForNat : Set -> Set
ArgForNat X = Σ[ b ∈ Bool ] (if b then ⊤ else X)

data ℕ : Set where
  zeroOrSuc : ArgForNat ℕ -> ℕ

pattern zero = zeroOrSuc (true , tt)
pattern suc n = zeroOrSuc (false , n)

pred : ℕ -> ℕ
pred zero = zero
pred (suc n) = n


{-

   What have we learnt?

   * (So-called inductive) data types are given by their constructors

   * ...so to describe them, it is enough to describe the constructors

   * ...and to describe them, it is enough to describe the type of arguments

   * can reduce the problem to describing a single argument by a function of
     type Set -> Set.

-}

---------------------------------------------------------------------------
-- A data type of data types
---------------------------------------------------------------------------

module DESC (U : Set)(El : U -> Set) where

  data Desc : Set where
    `⊤ : Desc
    `Σ : (a : U) -> (El a -> Desc) -> Desc
    _`×_ : Desc -> Desc -> Desc
    `X : Desc

  Args : Desc -> Set -> Set
  Args `⊤ X = ⊤
  Args (`Σ a b) X = Σ[ x ∈ El a ] (Args (b x) X)
  Args (c `× d) X = Args c X × Args d X
  Args `X X = X

  data ⟦_⟧Desc (d : Desc) : Set where
    con : Args d (⟦ d ⟧Desc) -> ⟦ d ⟧Desc

module _ where

  data U : Set where
    bool : U

  El : U -> Set
  El bool = Bool

  open DESC U El

  -- ArgForNat X = Σ[ b ∈ Bool ] (if b then ⊤ else X)

  natCode : Desc
  natCode = `Σ bool λ b → if b then `⊤ else `X

  ArgsForNat' = Args natCode

  ℕ' = ⟦ natCode ⟧Desc

  -- zero' : ℕ'
  pattern zero' = con (true , tt)

  -- suc' : ℕ' -> ℕ'
  pattern suc' n = con (false , n)

  pred' : ℕ' -> ℕ'
  pred' zero' = zero'
  pred' (suc' n) = n

{-
    What have we learnt?

    * Can describe operations Set -> Set by a *data type of data types* Desc

    * "Decoding" function Args : Desc -> (Set -> Set)

    * Generic data type ⟦ d ⟧Desc : Set for d : Desc

-}

---------------------------------------------------------------------------
-- Generic programming (= ordinary programming on descriptions)
---------------------------------------------------------------------------

-- It is tedious to prove over and over again that certain data types
-- are propositions. Let's do it once and for all!

module _ (U : Set)(El : U -> Set)(propU : {a : U} -> isPropositional (El a))  where

  open DESC U El

  isPropArgs : {c : Desc}(d : Desc) -> isPropositional (Args d ⟦ c ⟧Desc)
  isPropArgs `⊤ tt tt = refl
  isPropArgs (`Σ a b) (x , y) (x' , y') with propU x x'
  ... | refl = cong (x ,_) (isPropArgs (b x) y y')
  isPropArgs (d `× e) (x , y) (x' , y') = cong₂ _,_ (isPropArgs d x x') (isPropArgs e y y')
  isPropArgs `X (con x) (con y) = cong con (isPropArgs _ x y)

  genericIsProp : (d : Desc) -> isPropositional (⟦ d ⟧Desc)
  genericIsProp d (con x) (con y) = cong con (isPropArgs d x y)

-- Can also do the same for decidable equality

HasDecEq : Set -> Set
HasDecEq A = (x y : A) -> Dec (x ≡ y)

module _ (U : Set)(El : U -> Set)(decU : {a : U} -> HasDecEq (El a))  where

  open DESC U El

  genericDecArgs : {c : Desc}(d : Desc) -> HasDecEq (Args d ⟦ c ⟧Desc)
  genericDecArgs `⊤ tt tt = yes refl
  genericDecArgs (`Σ a b) (x , y) (x' , y') with decU x x'
  ... | no p = no λ { refl → p refl }
  ... | yes refl with genericDecArgs (b x) y y'
  ...            | yes q = yes (cong (x ,_) q)
  ...            | no q = no λ { refl → q refl }
  genericDecArgs (d `× e) (x , y) (x' , y') with genericDecArgs d x x'
  ... | no p = no λ { refl → p refl }
  ... | yes p with genericDecArgs e y y'
  ...         | no q = no λ { refl → q refl }
  ...         | yes q = yes (cong₂ _,_ p q)
  genericDecArgs `X (con x) (con y) with genericDecArgs _ x y
  ... | no p = no λ { refl → p refl }
  ... | yes p = yes (cong con p)

  genericDeqEq : (d : Desc) -> (x y : ⟦ d ⟧Desc) -> Dec (x ≡ y)
  genericDeqEq d (con x) (con y) with genericDecArgs d x y
  ... | no p = no λ { refl → p refl }
  ... | yes p = yes (cong con p)

{-
    What have we learnt?

    * Can write generic programs by pattern matching on Desc codes

    * Generic programming becomes ordinary programming!
-}

module NowYouTry.Derivability where

open import Data.String
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Data.Nat
open import Function

---------------------------------------------------------------------------
-- Inductively defined derivability
---------------------------------------------------------------------------

-- Formulas

data Formula : Set where
  Atom : String -> Formula
  _⇒_ : Formula -> Formula -> Formula

-- Contexts

data Context : Set where
  ε : Context
  _·_ : Context -> Formula -> Context -- \cdot

-- A proof system

data _⊢_ : Context -> Formula -> Set where -- \vdash
  hyp : ∀ {Γ A} → Γ · A ⊢ A
  weak : ∀ {Γ A B } → Γ ⊢ A → Γ · B ⊢ A
  abs : ∀ {Γ A B } → Γ · A ⊢ B →  Γ ⊢ A ⇒ B
  app : ∀ {Γ A B } → Γ ⊢ A ⇒ B →  Γ ⊢ A → Γ ⊢ B

example1 : ε · Atom "A" ⊢ Atom "A"
example1 = hyp

example2 : ε · Atom "A" · Atom "A" ⇒ Atom "B" ⊢ Atom "B"
example2 = app hyp (weak hyp)

 {-------------
  -- Summary --
  -------------}

  -- 1. Use inductive families to encode eg derivability and other
  -- treelike structures
  -- 2. Easy to show what *is* derivable but what about showing what isn't?

---------------------------------------------------------------------------
-- Semantics
---------------------------------------------------------------------------

--example3 : ¬ (ε ⊢ (Atom "A" ⇒ Atom "B") ⇒ Atom "A")
-- example3 (abs (weak (app (abs hyp) d₁))) = {!!}

Env = String -> Set

⟦_⟧F : Formula -> Env -> Set -- \[[
⟦ Atom x ⟧F ρ = ρ x
⟦ A ⇒ B ⟧F ρ = ⟦ A ⟧F ρ -> ⟦ B ⟧F ρ

⟦_⟧C : Context -> Env -> Set
⟦ ε ⟧C ρ = ⊤
⟦ Γ · A ⟧C ρ = ⟦ Γ ⟧C ρ × ⟦ A ⟧F ρ

-- soundness: every derivation has an interpretation
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A -> (ρ : Env) -> ⟦ Γ ⟧C ρ -> ⟦ A ⟧F ρ
⟦ hyp ⟧ ρ (γ , a) = a
⟦ weak d ⟧ ρ (γ , b) = ⟦ d ⟧ ρ γ
⟦ abs d ⟧ ρ γ = λ a → ⟦ d ⟧ ρ (γ , a)
⟦ app d e ⟧ ρ γ = ⟦ d ⟧ ρ γ (⟦ e ⟧ ρ γ)

example3 : ¬ (ε ⊢ (Atom "A" ⇒ Atom "B") ⇒ Atom "A")
example3 d = ⟦ d ⟧ ρ tt λ _ → tt
  where
    ρ : String -> Set
    ρ "A" = ⊥
    ρ "B" = ⊤
    ρ _  = ℕ

 {-------------
  -- Summary --
  -------------}

 -- 1. Can use a model to show what is *not* derivable
 -- 2. Soundness means everything provable is true in the model
 -- 3. (Completeness: if true in the model· then provable)

---------------------------------------------------------------------------
-- Meta-theoretical properties
---------------------------------------------------------------------------

-- Let's prove that we can replace abs + variables with just the S and
-- K combinators.

-- First, we define the alternative proof system:

data ⊢sk_ : Formula -> Set where
  app : ∀ {A B} → ⊢sk A ⇒ B → ⊢sk A → ⊢sk B
  K : ∀ {A B} → ⊢sk A ⇒ B ⇒ A
  S : ∀ {A B C} → ⊢sk (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C

-- look ma, no contexts!


-- We now want to translate `⊢sk A → ε ⊢ A` and `ε ⊢ A → ⊢sk A`

-- we can easily translate one way:

SKtoND : ∀ {A} → ⊢sk A -> ε ⊢ A
SKtoND (app d e) = app (SKtoND d) (SKtoND e)
SKtoND K = abs (abs (weak hyp))
SKtoND S = abs (abs (abs (app (app (weak (weak hyp)) hyp) (app (weak hyp) hyp))))

-- the other way looks promising, too:

{-
NDtoSK : ∀ {A} → ε ⊢ A -> ⊢sk A
NDtoSK (abs d) = {!NDtoSK d!}
NDtoSK (app d e) = app (NDtoSK d) (NDtoSK e)
-}

-- generalise!

{-
NDtoSK : ∀ {Γ A} → Γ ⊢ A -> ⊢sk A
NDtoSK hyp = {!!} -- not going to work, because ⊢sk A does not talk about Γ!
NDtoSK (weak d) = {!!}
NDtoSK (abs d) = {!!}
NDtoSK (app d d₁) = {!!}
-}

-- generalise to non-empty contexts!

-- Generalise ⊢sk A to take Γ into account too
data _⊢skv_ : Context -> Formula -> Set where
  hyp : ∀ {Γ A} → Γ · A ⊢skv A
  weak : ∀ {Γ A B } → Γ ⊢skv A → Γ · B ⊢skv A
  app : ∀ {Γ A B} → Γ ⊢skv A ⇒ B → Γ ⊢skv A → Γ ⊢skv B
  K : ∀ {Γ A B} → Γ ⊢skv A ⇒ B ⇒ A
  S : ∀ {Γ A B C} → Γ ⊢skv (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C

SKVtoSK : ∀ {A} → ε ⊢skv A -> ⊢sk A
SKVtoSK (app d e) = app (SKVtoSK d) (SKVtoSK e)
SKVtoSK K = K
SKVtoSK S = S

NDtoSKV : ∀ {Γ A} → Γ ⊢ A -> Γ ⊢skv A
NDtoSKV hyp = hyp
NDtoSKV (weak d) = weak (NDtoSKV d)
NDtoSKV (abs d) = absSK (NDtoSKV d)
  where
    absSK : ∀ {Γ A B } → Γ · A ⊢skv B →  Γ ⊢skv A ⇒ B
    absSK {A = A} hyp = app (app S K) (K {B = A})
    absSK (weak d) = app K d
    absSK (app d e) = app (app S (absSK d)) (absSK e)
    absSK K = app K K
    absSK S = app K S
NDtoSKV (app d e) = app (NDtoSKV d) (NDtoSKV e)

NDtoSK : ∀ {A} → ε ⊢ A -> ⊢sk A
NDtoSK = SKVtoSK ∘ NDtoSKV

 {-------------
  -- Summary --
  -------------}

 -- 1. Use pattern matching to prove things about the encoded logic itself
 -- 2. Here: S and K combinators can replace abstraction + application

---------------------------------------------------------------------------
-- Now You Try
---------------------------------------------------------------------------

-- Prove that `(B -> A) -> (A -> B)` is not provable in the SK calculus:

¬everythingEquivalent : ¬ (⊢sk (Atom "B" ⇒ Atom "A") ⇒ (Atom "A" ⇒ Atom "B"))
¬everythingEquivalent d = {!!}













-------------------
-- Fixety vodoo
-------------------

infix 3 ⊢sk_
infix 3 _⊢skv_
infix 3 _⊢_
infixl 4 _·_
infixr 6 _⇒_


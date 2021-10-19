module Tutorials.Week04 where

open import Data.List using (List; []; _∷_)
open import Data.Bool
open import Data.String
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Function
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Plan:
--   SK
--   Compare (with)
--   eq.reasoning
--   finer points of with



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
  hyp : ∀ {Γ A}                            →   Γ · A ⊢ A
  weak : ∀ {Γ A B } → Γ ⊢ A                →   Γ · B ⊢ A
  abs : ∀ {Γ A B }  → Γ · A ⊢ B            →   Γ ⊢ A ⇒ B
  app : ∀ {Γ A B }  → Γ ⊢ A ⇒ B →  Γ ⊢ A   →   Γ ⊢ B

ex-as-function : {A B : Set} → A → B → B
ex-as-function = λ a → λ b → b

ex : ε ⊢ Atom "A" ⇒ Atom "B" ⇒ Atom "B"
ex = abs (abs hyp)

-- Semantics

Env = String -> Set

⟦_⟧F : Formula -> Env -> Set -- \[[
⟦ Atom x ⟧F ρ = ρ x
⟦ A ⇒ B ⟧F ρ = ⟦ A ⟧F ρ -> ⟦ B ⟧F ρ

⟦_⟧C : Context -> Env -> Set
⟦ ε ⟧C ρ = ⊤
⟦ Γ · A ⟧C ρ = ⟦ Γ ⟧C ρ × ⟦ A ⟧F ρ

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A -> (ρ : Env) -> ⟦ Γ ⟧C ρ -> ⟦ A ⟧F ρ
⟦ hyp ⟧ ρ (γ , a) = a
⟦ weak d ⟧ ρ (γ , b) = ⟦ d ⟧ ρ γ
⟦ abs d ⟧ ρ γ = λ a → ⟦ d ⟧ ρ (γ , a)
⟦ app d e ⟧ ρ γ = ⟦ d ⟧ ρ γ (⟦ e ⟧ ρ γ)

ex-as-function' : {A B : Set} → A → B → B
ex-as-function' {A} {B} = ⟦ ex ⟧ ρ tt where
  ρ : String -> Set
  ρ "A" = A
  ρ "B" = B
  ρ x = ℕ

ex-as-function'=ex-as-function : {A B : Set} →
  ex-as-function' {A} {B} ≡ ex-as-function {A} {B}
ex-as-function'=ex-as-function = refl

example3 : ¬ (ε ⊢ (Atom "A" ⇒ Atom "B") ⇒ Atom "A")
example3 d = ⟦ d ⟧ ρ tt λ _ → 42 -- ⟦ d ⟧ ρ tt λ _ → tt
  where
    ρ : String -> Set
    ρ "A" = ⊥
    ρ "B" = ℕ
    ρ _  = ℕ

-- S and K combinators
k : {A B : Set} → A -> B -> A
k = λ a → λ b → a

s : {A B C : Set} → (A -> B -> C) -> (A -> B) -> (A -> C)
s = λ f → λ g → λ a → (f a) (g a)

data ⊢sk_ : Formula -> Set where
  app : ∀ {A B} → ⊢sk A ⇒ B → ⊢sk A → ⊢sk B
  K : ∀ {A B} → ⊢sk A ⇒ B ⇒ A
  S : ∀ {A B C} → ⊢sk (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C

SKtoND : ∀ {A} → ⊢sk A -> ε ⊢ A
SKtoND (app d e) = app (SKtoND d) (SKtoND e)
SKtoND K = abs (abs (weak hyp))
SKtoND S = abs (abs (abs (app (app (weak (weak hyp)) hyp) (app (weak hyp) hyp))))

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

infix 3 ⊢sk_
infix 3 _⊢skv_
infix 3 _⊢_
infixl 4 _·_
infixr 6 _⇒_

data Compare : (x y : ℕ) → Set where
  lt : (x d : ℕ) → Compare x (x + suc d)
  eq : (x : ℕ) -> Compare x x
  gt : (x d : ℕ) → Compare (x + suc d) x

compare : (x y : ℕ) → Compare x y
compare zero zero = eq zero
compare zero (suc y) = lt zero y
compare (suc x) zero = gt zero x
compare (suc x) (suc y) with compare x y
compare (suc x) (suc .(x + suc d)) | lt .x d = lt (suc x) d
compare (suc x) (suc .x) | eq .x = eq (suc x)
compare (suc .(y + suc y₁)) (suc y) | gt .y y₁ = gt (suc y) y₁

max : (x y : ℕ) → ℕ
max x y with compare x y
max x .(x + suc y)  | lt .x y  = (x + suc y)
max x .x            | eq .x    = x
max .(y + suc y') y | gt .y y' = y + suc y'

compare-eq : ∀ x → compare x x ≡ eq x
compare-eq zero = refl
compare-eq (suc x) with compare x x | compare-eq x
... | .(eq x) | refl = refl

max-eq : ∀ x → max x x ≡ x
max-eq x with compare x x | compare-eq x
... | .(eq x) | refl = refl

-- Similarly (no time in the tutorial) ----------------
compare-gt : ∀ x d → compare (x + suc d) x ≡ gt x d
compare-gt zero d = refl
compare-gt (suc x) d with compare (x + suc d) x | compare-gt x d
... | .(gt x d) | refl = refl

compare-lt : ∀ x d → compare x (x + suc d) ≡ lt x d
compare-lt zero d = refl
compare-lt (suc x) d with compare x (x + suc d) | compare-lt x d
... | .(lt x d) | refl = refl

max-sym : ∀ x y → max x y ≡ max y x
max-sym x y with compare x y
max-sym x y | lt .x d with compare (x + suc d) x | compare-gt x d
max-sym x .(x + suc d) | lt .x d | .(gt x d) | refl = refl
max-sym x y | eq .x = sym (max-eq x)
max-sym x y | gt .y d with compare y (y + suc d) | compare-lt y d
max-sym .(y + suc d) y | gt .y d | .(lt y d) | refl = refl
-------------------------------------------------------

lemma : ∀ x y → max (max x y) (max y x) ≡ max x y
lemma x y = begin
  max (max x y) (max y x)
    ≡⟨ cong (λ z → max z (max y x)) (max-sym x y) ⟩
  max (max y x) (max y x)
    ≡⟨ max-eq (max y x) ⟩
  max y x
    ≡⟨ max-sym y x ⟩
  max x y
    ∎














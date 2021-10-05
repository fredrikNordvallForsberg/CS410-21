module Tutorials.Week02 where

open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

-- Correct opinion: cat good doggo good

-- Why is A × B "just" Σ[ _ ∈ A ] B?

P : ℕ → Set
P zero = Bool
P (suc n) = Bool → P n

pairNatP : Σ ℕ (λ n → P n)
pairNatP = (3 , λ x y z → x)

pairNatBool : Σ ℕ (λ n → Bool)
pairNatBool = (3 , false)

pairNatBool' : ℕ × Bool
pairNatBool' = (3 , false)


-- Why is A → B "just" (_ : A) → B?

funNatP : (n : ℕ) → P n
funNatP zero = false
funNatP (suc n)  = λ b → funNatP n

funNatBool : (n : ℕ) → Bool
funNatBool zero = false
funNatBool (suc n) = true

funNatBool' : ℕ → Bool
funNatBool' zero = false
funNatBool' (suc n) = true

-- How to use equational reasoning

open ≡-Reasoning -- \==

accMult : ℕ → ℕ → ℕ → ℕ
accMult zero m acc = acc
accMult (suc n) m acc = accMult n m (m + acc)

mult : ℕ → ℕ → ℕ
mult n m = accMult n m 0

-- Solve all goals with as much normalisation as possible: C-u C-u C-c C-s

accMultCorrect : (n m acc : ℕ) → accMult n m acc ≡ n * m + acc
accMultCorrect zero m acc = refl
accMultCorrect (suc n) m acc = begin
  accMult n m (m + acc)
    ≡⟨ accMultCorrect n m (m + acc) ⟩
  n * m + (m + acc)
    ≡⟨ sym (+-assoc (n * m) m acc) ⟩
  (n * m + m) + acc
    ≡⟨ cong (λ z → z + acc) (+-comm (n * m) m)  ⟩
  (m + n * m) + acc
    ∎ -- \qed

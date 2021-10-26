module Tutorials.Week05 where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Lectures.Hutton

-- Going forward compromise: Now-You-Try solutions if you ask for them

-- "A stitch in time saves nine"

-- Plan:
--   cfold: why do we need to specify non-num cases?
--   eval-if
--   rewrites and equality

cfold : ∀ {t} → TExpr t -> TExpr t
cfold (num x) = num x
cfold (bit x) = bit x
cfold (e +E e') with cfold e | cfold e'
... | num n | num n' = num (n + n')
... | ce    | ce'    = ce +E ce'
cfold (ifE e then e' else e'') = ifE cfold e then cfold e' else cfold e''

e : TExpr nat
e = (ifE bit true then num 7 +E num 5 else num 13) +E num 8

-- How does rewrite work?

+0 : (n : ℕ) -> n + 0 ≡ n
+0 zero = refl
+0 (suc n) rewrite +0 n = refl
{-
Original Goal:
  suc (n + 0) ≡ suc n
      ^^^^^^^
New goal:
  suc       n ≡ suc n
            ~
Have:
  +0 n : n + 0 ≡ n
         ^^^^^   ~
-}

-- rewrite is implemented as this behind the scenes:

+0' : (n : ℕ) -> n + 0 ≡ n
+0' zero = refl
+0' (suc n) with n + 0 | +0' n
... | .n | refl = refl

-- with is implemented as this behind the scenes:

+0'' : (n : ℕ) -> n + 0 ≡ n
+0'' zero = refl
+0'' (suc n) = helper n (n + 0) (+0'' n)
  where
    helper : (n : ℕ)(x : ℕ)(qq : x ≡ n) -> suc x ≡ suc n
    helper n .n refl = refl

-- Another equality example:

cfold-idempotent : ∀ {t} → (e : TExpr t) → cfold (cfold e) ≡ cfold e
cfold-idempotent (num x) = refl
cfold-idempotent (bit x) = refl
cfold-idempotent (e +E e') with cfold e | cfold e' |
                                cfold-idempotent e | cfold-idempotent e'
... | num n | num n' | _ | _ = refl
... | num x | ce' +E ce'' | p | q rewrite q = refl
... | num x | ifE ce' then ce'' else ce''' | p | q rewrite q = refl
... | ce +E ce₁ | num x | p | q rewrite p = refl
... | ce +E ce₁ | ce' +E ce'' | p | q rewrite p | q = refl
... | ce +E ce₁ | ifE ce' then ce'' else ce''' | p | q rewrite p | q = refl
... | ifE ce then ce₁ else ce₂ | num x | p | q rewrite p = refl
... | ifE ce then ce₁ else ce₂ | ce' +E ce'' | p | q rewrite p | q = refl
... | ifE ce then ce₁ else ce₂ | ifE ce' then ce'' else ce''' | p | q rewrite p | q = refl
-- {- Other ways to do it: -}
-- cfold-idempotent (ifE e then e' else e'') rewrite cfold-idempotent e | cfold-idempotent e' | cfold-idempotent e'' = refl
{-
cfold-idempotent (ifE e then e' else e'') =
  trans (cong (λ z → ifE z then  cfold (cfold e') else cfold (cfold e''))
              (cfold-idempotent e))
        (trans (cong (λ z → ifE cfold e then z else cfold (cfold e''))
                     (cfold-idempotent e'))
               (cong (λ z → ifE cfold e then cfold e' else z) (cfold-idempotent e'')))
-}
cfold-idempotent (ifE e then e' else e'') = begin
  (ifE cfold (cfold e) then cfold (cfold e') else cfold (cfold e''))
    ≡⟨ cong (λ z → ifE z then cfold (cfold e') else cfold (cfold e'')) (cfold-idempotent e) ⟩
  (ifE cfold e then cfold (cfold e') else cfold (cfold e''))
    ≡⟨ (cong (λ z → ifE cfold e then z else cfold (cfold e'')) (cfold-idempotent e')) ⟩
  (ifE cfold e then cfold e' else cfold (cfold e''))
    ≡⟨ (cong (λ z → ifE cfold e then cfold e' else z) (cfold-idempotent e'')) ⟩
  (ifE cfold e then cfold e' else cfold e'')
    ∎

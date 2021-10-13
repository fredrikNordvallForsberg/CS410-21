module NowYouTry.HuttonOptimised where

open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties
open import Data.Bool hiding (_≟_)
open import Data.Maybe hiding (decToMaybe)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Lectures.Hutton

---------------------------------------------------------------------------
-- Optimising expressions
---------------------------------------------------------------------------

cfold : ∀ {t} → TExpr t -> TExpr t
cfold (num x) = num x
cfold (bit x) = bit x
cfold (e +E e') with cfold e | cfold e'
... | num n | num n' = num (n + n')
... | ce    | ce'    = ce +E ce'
cfold (ifE e then e' else e'') = ifE cfold e then cfold e' else cfold e''

---------------
-- Summary
---------------

-- * We optimise expressions by implementing a function TExpr t -> TExpr t
-- * Don't forget to also optimise deep recursive calls!



---------------------------------------------------------------------------
-- Proving constant folding correct
---------------------------------------------------------------------------

cfold-sound : ∀ {t} → (e : TExpr t) -> teval (cfold e) ≡ teval e
cfold-sound (num x) = refl
cfold-sound (bit x) = refl
cfold-sound (e +E e') with cfold e | cfold e' | cfold-sound e | cfold-sound e'
... | num n | num n' | p | q = cong₂ _+_ p q
... | num x | ce' +E ce'' | p | q = cong₂ _+_ p q
... | num x | ifE ce' then ce'' else ce''' | p | q = cong₂ _+_ p q
... | ce +E ce₁ | num x | p | q = cong₂ _+_ p q
... | ce +E ce₁ | ce' +E ce'' | p | q = cong₂ _+_ p q
... | ce +E ce₁ | ifE ce' then ce'' else ce''' | p | q = cong₂ _+_ p q
... | ifE ce then ce₁ else ce₂ | num x | p | q = cong₂ _+_ p q
... | ifE ce then ce₁ else ce₂ | ce' +E ce'' | p | q = cong₂ _+_ p q
... | ifE ce then ce₁ else ce₂ | ifE ce' then ce'' else ce''' | p | q = cong₂ _+_ p q
cfold-sound(ifE e then e' else e'') rewrite cfold-sound e | cfold-sound e' | cfold-sound e'' = refl

---------------
-- Summary
---------------

-- * Follow the same structure of the program, with the same 'with's
-- * You need to expand all catch-alls for Agda to see that they are not the real cases
--   (is there a better way?)



---------------------------------------------------------------------------
-- Using views: the remove + 0 optimisation
---------------------------------------------------------------------------

data Zeroness : (e e' : TExpr nat) -> Set where
  both : Zeroness (num 0) (num 0)
  left : (e' : TExpr nat) -> Zeroness (num 0) e'
  right : (e : TExpr nat) -> Zeroness e (num 0)
  neither : (e e' : TExpr nat) -> Zeroness e e'

zeroness : (e e' : TExpr nat) -> Zeroness e e'
zeroness (num 0) (num 0) = both
zeroness (num 0) e' = left e'
zeroness e (num 0) = right e
zeroness e e' = neither e e'

remove+0 : ∀ {t} → TExpr t -> TExpr t
remove+0 (num n) = num n
remove+0 (bit b) = bit b
remove+0 (e +E e') with remove+0 e | remove+0 e' | zeroness (remove+0 e) (remove+0 e')
... | _ | _ | both = num 0
... | _ | _ | left re' = re'
... | _ | _ | right re = re
... | _ | _ | neither re re' = re +E re'
remove+0 (ifE e then e' else e'') = ifE remove+0 e then remove+0 e' else remove+0 e''

remove+0-sound : ∀ {t} → (e : TExpr t) -> teval (remove+0 e) ≡ teval e
remove+0-sound (num x) = refl
remove+0-sound (bit x) = refl
remove+0-sound (e +E e') with remove+0 e | remove+0 e' | zeroness (remove+0 e) (remove+0 e') | remove+0-sound e | remove+0-sound e'
... | _ | _ | both | p | q rewrite sym p | sym q = refl
... | _ | _ | left _ | p | q rewrite sym p | sym q = refl
... | _ | _ | right _ | p | q rewrite sym p | sym q = sym (+-identityʳ _)
... | _ | _ | neither _ _ | p | q rewrite sym p | sym q = refl
remove+0-sound (ifE e then e' else e'')
  rewrite remove+0-sound e | remove+0-sound e' | remove+0-sound e'' = refl


---------------
-- Summary
---------------

-- * A view: an indexed datatype V : A -> B -> ... -> Set with
--   constructors all the cases of interest, plus a "catch-all
--   constructor", and a function view : (a : A) -> (b : B) -> ... -> V a b ...

-- * Used as 'with view a b ...'

-- * Means that we only have to consider interesting cases + catchall, even in proofs

-- * Might need to with on argument expressions, to generalise them
--   sufficently, and on recursive calls, to make the termination checker happy

---------------------------------------------------------------------------
-- Now You try
---------------------------------------------------------------------------

-- Implement an optimisation which replaces "if true then e else e'"
-- by e and "if false then e else e'" by e'. You can either construct
-- a view, or do it by hand (it doesn't really matter, since TExpr bool
-- is limited).

eval-if : ∀ {t} → TExpr t -> TExpr t
eval-if e = {!!}

-- Prove that it is sound.

-- HINT: You also need to 'with' on eval-if-sound e in the interesting
-- case, to get something to rewrite along (after symming it).

eval-if-sound : ∀ {t} → (e : TExpr t) -> teval (eval-if e) ≡ teval e
eval-if-sound e = {!!}


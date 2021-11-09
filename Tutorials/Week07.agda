{-# OPTIONS --type-in-type #-}
module Tutorials.Week07 where

open import Relation.Binary.PropositionalEquality

open import Common.Category

open Category
open Functor

-- A small category

-- I declare the set of objects of the category (I add primes to the
-- names to not confuse myself and Agda when saying "Consider an
-- object A" (where A is a variable)
data MyObj : Set where
  A' B' C' D' : MyObj

-- I declare the set of morphisms, given with their input and output objects
data MyMor : MyObj -> MyObj -> Set where
  f' : MyMor A' B'
  g' : MyMor B' C'
  h' : MyMor B' C'
  k' : MyMor D' C'
  l' : MyMor A' C'
  -- we could add idA : MyMor A' A', idB : MyMor B' B' etc, but let's do it all in one swoop (fell or not)
  Id : (X : MyObj) → MyMor X X

-- Then we define our Category. By "pattern matching on the result
-- type" (C-c C-c Enter), Agda tells us what we need to provide.
MyCat : Category
Obj MyCat = MyObj
Hom MyCat = MyMor
id MyCat {X} = Id X
-- We have to define the composition, which we do guided by our
-- on-paper drawing
comp MyCat {.A'} {.B'} {.C'} f' g' = l'
comp MyCat {.A'} {.B'} {.C'} f' h' = l'
comp MyCat f (Id X) = f
comp MyCat (Id X) g = g
-- Then we have to prove the laws. For a concrete small category such
-- as this, that typically means just considering all possibilities
-- and verifying that they are okay.
assoc MyCat {f = f'} {g'} {Id .C'} = refl
assoc MyCat {f = f'} {h'} {Id .C'} = refl
assoc MyCat {f = f'} {Id .B'} {g'} = refl
assoc MyCat {f = f'} {Id .B'} {h'} = refl
assoc MyCat {f = f'} {Id .B'} {Id .B'} = refl
assoc MyCat {f = g'} {Id .C'} {Id .C'} = refl
assoc MyCat {f = h'} {Id .C'} {Id .C'} = refl
assoc MyCat {f = k'} {Id .C'} {Id .C'} = refl
assoc MyCat {f = l'} {Id .C'} {Id .C'} = refl
assoc MyCat {f = Id .A'} {f'} {g'} = refl
assoc MyCat {f = Id .A'} {f'} {h'} = refl
assoc MyCat {f = Id .A'} {f'} {Id .B'} = refl

assoc MyCat {f = Id .B'} {g'} {Id .C'} = refl
assoc MyCat {f = Id .B'} {h'} {Id .C'} = refl
assoc MyCat {f = Id .D'} {k'} {Id .C'} = refl
assoc MyCat {f = Id .A'} {l'} {Id .C'} = refl
assoc MyCat {f = Id .A'} {Id .A'} {f'} = refl
assoc MyCat {f = Id .B'} {Id .B'} {g'} = refl
assoc MyCat {f = Id .B'} {Id .B'} {h'} = refl
assoc MyCat {f = Id .D'} {Id .D'} {k'} = refl
assoc MyCat {f = Id .A'} {Id .A'} {l'} = refl
assoc MyCat {f = Id _} {Id _} {Id _} = refl
identityˡ MyCat {f = f'} = refl
identityˡ MyCat {f = g'} = refl
identityˡ MyCat {f = h'} = refl
identityˡ MyCat {f = k'} = refl
identityˡ MyCat {f = l'} = refl
identityˡ MyCat {f = Id _} = refl
identityʳ MyCat {f = f'} = refl
identityʳ MyCat {f = g'} = refl
identityʳ MyCat {f = h'} = refl
identityʳ MyCat {f = k'} = refl
identityʳ MyCat {f = l'} = refl
identityʳ MyCat {f = Id _} = refl


-- Here is another category, so that we can define a functor between them
data MyOtherObj : Set where
  X' Y' Z' : MyOtherObj

data MyOtherMor : MyOtherObj → MyOtherObj -> Set where
  x' : MyOtherMor X' Y'
  y' : MyOtherMor Z' Y'
  Id' : (X : MyOtherObj) -> MyOtherMor X X

MyOtherCat : Category
Obj MyOtherCat = MyOtherObj
Hom MyOtherCat = MyOtherMor
id MyOtherCat {X} = Id' X
comp MyOtherCat x' (Id' .Y') = x'
comp MyOtherCat y' (Id' .Y') = y'
comp MyOtherCat (Id' .X') x' = x'
comp MyOtherCat (Id' .Z') y' = y'
comp MyOtherCat (Id' _) (Id' _) = Id' _
assoc MyOtherCat {f = x'} {Id' .Y'} {Id' .Y'} = refl
assoc MyOtherCat {f = y'} {Id' .Y'} {Id' .Y'} = refl
assoc MyOtherCat {f = Id' .X'} {x'} {Id' .Y'} = refl
assoc MyOtherCat {f = Id' .Z'} {y'} {Id' .Y'} = refl
assoc MyOtherCat {f = Id' .X'} {Id' .X'} {x'} = refl
assoc MyOtherCat {f = Id' .Z'} {Id' .Z'} {y'} = refl
assoc MyOtherCat {f = Id' _} {Id' _} {Id' _} = refl
identityˡ MyOtherCat {f = x'} = refl
identityˡ MyOtherCat {f = y'} = refl
identityˡ MyOtherCat {f = Id' _} = refl
identityʳ MyOtherCat {f = x'} = refl
identityʳ MyOtherCat {f = y'} = refl
identityʳ MyOtherCat {f = Id' _} = refl


-- And here we define a functor, sending objects to objects and
-- morphisms to morphisms. Again by pattern matching on the result,
-- Agda tells us what we need to provide.
MyFun : Functor MyCat MyOtherCat
-- An action on objects:
act MyFun A' = X'
act MyFun B' = Y'
act MyFun C' = Y'
act MyFun D' = Z'
-- A mapping on morhpisms:
fmap MyFun {.A'} {.B'} f' = x'
fmap MyFun {.B'} {.C'} g' = Id' _
fmap MyFun {.B'} {.C'} h' = Id' _
fmap MyFun {.D'} {.C'} k' = y'
fmap MyFun {.A'} {.C'} l' = x'
fmap MyFun {S} {.S} (Id .S) = Id' _
-- Proof that we preserve identities:
identity MyFun = refl
-- Proof that we preserve compositions:
homomorphism MyFun {f = f'} {g'} = refl
homomorphism MyFun {f = f'} {h'} = refl
homomorphism MyFun {f = f'} {Id .B'} = refl
homomorphism MyFun {f = g'} {Id .C'} = refl
homomorphism MyFun {f = h'} {Id .C'} = refl
homomorphism MyFun {f = k'} {Id .C'} = refl
homomorphism MyFun {f = l'} {Id .C'} = refl
homomorphism MyFun {f = Id .A'} {f'} = refl
homomorphism MyFun {f = Id .B'} {g'} = refl
homomorphism MyFun {f = Id .B'} {h'} = refl
homomorphism MyFun {f = Id .D'} {k'} = refl
homomorphism MyFun {f = Id .A'} {l'} = refl
homomorphism MyFun {f = Id _} {Id _} = refl


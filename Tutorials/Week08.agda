{-# OPTIONS --type-in-type #-}
module Tutorials.Week08 where

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Common.Category
open import Lectures.Categories

-- open Category
open Functor
open NaturalTransformation
open Monad

-- nat trans

data MyObj : Set where
  A' B' : MyObj

data MyHom : MyObj -> MyObj -> Set where
  f' : MyHom A' B'
  idA : MyHom A' A'
  idB : MyHom B' B'

C : Category
Category.Obj C = MyObj
Category.Hom C = MyHom
--------------------------
Category.id C {A'} = idA
Category.id C {B'} = idB
--------------------------
Category.comp C f idB = f
Category.comp C idA f = f
--------------------------
Category.assoc C {f = f} {g} {h} = lemma-assoc f g h where
  lemma-assoc : {X Y Z W : MyObj} → (f : MyHom X Y)(g : MyHom Y Z)(h : MyHom Z W) →
                Category.comp C f (Category.comp C g h) ≡ Category.comp C (Category.comp C f g) h
  lemma-assoc f' g idB = refl
  lemma-assoc idA f' idB = refl
  lemma-assoc idA idA f' = refl
  lemma-assoc idA idA idA = refl
  lemma-assoc idB idB idB = refl
Category.identityˡ C {f = f} = lemma-idleft f where
  lemma-idleft : {X Y : MyObj} → (f : MyHom X Y) → Category.comp C f (Category.id C) ≡ f
  lemma-idleft f' = refl
  lemma-idleft idA = refl
  lemma-idleft idB = refl
Category.identityʳ C {f = f} = lemma-idright f where
  lemma-idright : {X Y : MyObj} → (f : MyHom X Y) → Category.comp C (Category.id C) f ≡ f
  lemma-idright f' = refl
  lemma-idright idA = refl
  lemma-idright idB = refl



data MyObj2 : Set where
  X' Y' Z' : MyObj2

data MyHom2 : MyObj2 -> MyObj2 -> Set where
  yx : MyHom2 Y' X'
  zx : MyHom2 Z' X'
  yz : MyHom2 Y' Z'
  id' : (O : MyObj2) → MyHom2 O O

D : Category
Category.Obj D = MyObj2
Category.Hom D = MyHom2
Category.id D = id' _
Category.comp D (id' _) g = g
Category.comp D f (id' _) = f
Category.comp D yz zx = yx
Category.assoc D {f = yx} {id' .X'} {id' .X'} = refl
Category.assoc D {f = zx} {id' .X'} {id' .X'} = refl
Category.assoc D {f = yz} {zx} {id' .X'} = refl
Category.assoc D {f = yz} {id' .Z'} {zx} = refl
Category.assoc D {f = yz} {id' .Z'} {id' .Z'} = refl
Category.assoc D {f = id' .Y'} {yx} {id' .X'} = refl
Category.assoc D {f = id' .Z'} {zx} {id' .X'} = refl
Category.assoc D {f = id' .Y'} {yz} {zx} = refl
Category.assoc D {f = id' .Y'} {yz} {id' .Z'} = refl
Category.assoc D {f = id' .Y'} {id' .Y'} {yx} = refl
Category.assoc D {f = id' .Z'} {id' .Z'} {zx} = refl
Category.assoc D {f = id' .Y'} {id' .Y'} {yz} = refl
Category.assoc D {f = id' _} {id' _} {id' _} = refl
Category.identityˡ D {f = yx} = refl
Category.identityˡ D {f = zx} = refl
Category.identityˡ D {f = yz} = refl
Category.identityˡ D {f = id' _} = refl
Category.identityʳ D {f = f} = refl

F : Functor C D
-------------------- Action on objects -----------
act F A' = Y'
act F B' = X'
-------------------- Map on morphisms ------------
fmap F f' = yx
fmap F idA = id' Y'
fmap F idB = id' X'
--------------------------------------------------
identity F {A'} = refl
identity F {B'} = refl
homomorphism F {f = f'} {idB} = refl
homomorphism F {f = idA} {f'} = refl
homomorphism F {f = idA} {idA} = refl
homomorphism F {f = idB} {idB} = refl

G : Functor C D
-------------------- Action on objects -----------
act G A' = Z'
act G B' = X'
-------------------- Map on morphisms ------------
fmap G f' = zx
fmap G idA = id' Z'
fmap G idB = id' X'
--------------------------------------------------
identity G {A'} = refl
identity G {B'} = refl
homomorphism G {f = f'} {idB} = refl
homomorphism G {f = idA} {f'} = refl
homomorphism G {f = idA} {idA} = refl
homomorphism G {f = idB} {idB} = refl

nt : NaturalTransformation F G
transform nt A' = yz
transform nt B' = id' X'
natural nt .A' .B' f' = refl
natural nt .A' .A' idA = refl
natural nt .B' .B' idB = refl

module _ (R : Set) where

  Reader : Monad SET
  act (functor Reader) X = R -> X
  fmap (functor Reader) f a r = f (a r)
  identity (functor Reader) = refl
  homomorphism (functor Reader) = refl
  transform (returnNT Reader) X x _ = x
  natural (returnNT Reader) X Y f = refl
  transform (joinNT Reader) X x r = x r r
  natural (joinNT Reader) X Y f = refl
  returnJoin Reader = refl
  mapReturnJoin Reader = refl
  joinJoin Reader = refl

module _ (W : Set)(default : W)(combine : W → W → W)
         (identityˡ : ∀ w → combine w default ≡ w)
         (identityʳ : ∀ w → combine default w ≡ w)
         (assoc : ∀ w w' w'' → combine w'' (combine w' w) ≡ combine (combine w'' w') w)
  where

  -- (W, default, combine) must be a monoid!

  Writer : Monad SET
  act (functor Writer) X = X × W
  fmap (functor Writer) f (a , w) = (f a , w)
  identity (functor Writer) = refl
  homomorphism (functor Writer) = refl
  transform (returnNT Writer) X x = (x , default)
  natural (returnNT Writer) X Y f = refl
  transform (joinNT Writer) X ((x , w') , w) = x , combine w' w
  natural (joinNT Writer) X Y f = refl
  returnJoin Writer = ext λ { (x , w) → cong (λ z → (x , z)) (identityˡ w) }
  mapReturnJoin Writer = ext λ { (x , w) → cong (λ z → (x , z)) (identityʳ w) }
  joinJoin Writer = ext λ { (((x , w'') , w') , w) → cong (λ z → (x , z)) (assoc _ _ _) }

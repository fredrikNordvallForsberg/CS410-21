module NowYouTry.Kleisli where


open import Data.Nat hiding (_≤_)
open import Data.Product
open import Data.Sum
open import Data.List as List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality
open import Function hiding (_∘_; id)

open import Lectures.FunctorsAndNatTransformations
open import Lectures.Categories

open import Common.Category hiding (Monad)

open import Lectures.Monads

---------------------------------------------------------------------------
-- Using the categories solver
---------------------------------------------------------------------------

open import Common.Category.Solver

module _ {C : Category} where

  open Category C
  open Functor

{-

      F (id ∘ f)
  F X ----------> F X
   |  \          ^ |
   |   ---------/  |
 g |     F f       | g
   |               |
   v     F h       v      F k
  F Y ----------> F Y ----------> F Z
   |                               ^
   \------------------------------/
           F (h ∘ k)
-}


  example : {X Y Z : Obj}(F : Functor C C) ->
            (f : Hom X X)(g : Hom (act F X) (act F Y))(h : Hom Y Y)(k : Hom Y Z) ->
            (assumption : g ∘ fmap F f ≡ fmap F h ∘ g) ->
            fmap F k ∘ (g ∘ fmap F (id ∘ f)) ≡ fmap F (k ∘ h) ∘ g
  example F f g h k p = C ⊧begin
    fmapSyn F < k > ∘Syn (< g > ∘Syn fmapSyn F (idSyn ∘Syn < f >))
      ≡⟦ solveCat refl ⟧
    fmapSyn F < k > ∘Syn -[ < g > ∘Syn fmapSyn F < f > ]-
      ≡⟦ reduced (rd , rq p) ⟧
    fmapSyn F < k > ∘Syn -[ fmapSyn F < h > ∘Syn < g > ]-
      ≡⟦ solveCat refl ⟧
    fmapSyn F (< k > ∘Syn < h >) ∘Syn < g >
      ⟦∎⟧


---------------------------------------------------------------------------
-- Kleisli categories
---------------------------------------------------------------------------

module _ {C : Category} where

  open Monad
  open NaturalTransformation

  Kleisli : Monad C -> Category
  Category.Obj (Kleisli M) = Obj where open Category C
  Category.Hom (Kleisli M) X Y = Hom X (act M Y) where open Category C
  Category.id (Kleisli M) {X} = return M X
  Category.comp (Kleisli M) f g = join M _ ∘ fmap M g ∘ f where open Category C
  Category.assoc (Kleisli M) {f = f} {g} {h} = C ⊧begin
    < join M _ > ∘Syn fmapSyn (functor M) (< join M _ > ∘Syn fmapSyn (functor M) < h > ∘Syn < g >) ∘Syn < f >
      ≡⟦ solveCat refl ⟧
    -[ < join M _ > ∘Syn fmapSyn (functor M) < join M _ > ]- ∘Syn fmapSyn (functor M) (fmapSyn (functor M) < h >) ∘Syn fmapSyn (functor M) < g > ∘Syn < f >
      ≡⟦ reduced (rq (sym (joinJoin M)) , rd , rd , rd) ⟧
    -[ < join M _ > ∘Syn < join M _ > ]- ∘Syn fmapSyn (functor M) (fmapSyn (functor M) < h >) ∘Syn fmapSyn (functor M) < g > ∘Syn < f >
      ≡⟦ solveCat refl ⟧
    < join M _ > ∘Syn -[ < join M _ > ∘Syn fmapSyn (functor M) (fmapSyn (functor M) < h >) ]- ∘Syn fmapSyn (functor M) < g > ∘Syn < f >
      ≡⟦ reduced (rd , rq (natural (joinNT M) _ _ h) , rd , rd) ⟧
    < join M _ > ∘Syn -[ fmapSyn (functor M) < h > ∘Syn < join M _ > ]- ∘Syn fmapSyn (functor M) < g > ∘Syn < f >
      ≡⟦ solveCat refl ⟧
    < join M _ > ∘Syn fmapSyn (functor M) < h > ∘Syn < join M _ > ∘Syn fmapSyn (functor M) < g > ∘Syn < f >
      ⟦∎⟧ where open Category C
  Category.identityˡ (Kleisli M) {f = f} = C ⊧begin
    < join M _ > ∘Syn fmapSyn (functor M) < return M _ > ∘Syn < f >
      ≡⟦ solveCat refl ⟧
    -[ < join M _ > ∘Syn fmapSyn (functor M) < return M _ > ]- ∘Syn < f >
      ≡⟦ reduced (rq (mapReturnJoin M) , rd) ⟧
    -[ idSyn ]- ∘Syn < f >
      ≡⟦ solveCat refl ⟧
    < f >
      ⟦∎⟧
  Category.identityʳ (Kleisli M) {f = f} = C ⊧begin
    < join M _ > ∘Syn fmapSyn (functor M) < f > ∘Syn < return M _ >
      ≡⟦ solveCat refl ⟧
    < join M _ > ∘Syn -[ fmapSyn (functor M) < f > ∘Syn < return M _ > ]-
      ≡⟦ reduced (rd , rq (sym (natural (returnNT M) _ _ f))) ⟧
    < join M _ > ∘Syn -[ < return M _ > ∘Syn < f > ]-
      ≡⟦ solveCat refl ⟧
    -[ < join M _ > ∘Syn < return M _ > ]- ∘Syn < f >
      ≡⟦ reduced (rq (returnJoin M) , rd) ⟧
    -[ idSyn ]- ∘Syn < f >
      ≡⟦ solveCat refl ⟧
    < f >
      ⟦∎⟧

---------------------------------------------------------------------------
-- Now you try
---------------------------------------------------------------------------

  EmbedKleisli : (M : Monad C) -> Functor C (Kleisli M)
  Functor.act (EmbedKleisli M) X = X
  Functor.fmap (EmbedKleisli M) f = return M _ ∘ f where open Category C
  Functor.identity (EmbedKleisli M) = C ⊧begin
    < return M _ > ∘Syn idSyn
      ≡⟦ {!!} ⟧
    < return M _ >
      ⟦∎⟧
  Functor.homomorphism (EmbedKleisli M) {f = f} {g = g} = C ⊧begin
    < return M _ > ∘Syn (< g > ∘Syn < f > )
      ≡⟦ {!!} ⟧
    < join M _ > ∘Syn (fmapSyn (functor M) (< return M _ > ∘Syn < g > ) ∘Syn (< return M _ > ∘Syn < f > ))
      ⟦∎⟧

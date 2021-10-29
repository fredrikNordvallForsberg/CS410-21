{-# OPTIONS --type-in-type #-}
module NowYouTry.Monads where

open import Data.Nat hiding (_≤_)
open import Data.Product
open import Data.Sum
open import Data.List as List
open import Data.List.Properties hiding (concat-++)
open import Relation.Binary.PropositionalEquality
open import Function hiding (_∘_; id)

open import Lectures.FunctorsAndNatTransformations
open import Lectures.Categories

open import Common.Category hiding (Monad; idFunctor; compFunctor)
open import Common.Category.Solver



---------------------------------------------------------------------------
-- Monads, categorically
---------------------------------------------------------------------------

record Monad (C : Category) : Set where
  open Category C
  open Functor

  field
    functor : Functor C C

  private
    M = functor

  field
    returnNT : NaturalTransformation idFunctor M
    joinNT   : NaturalTransformation (compFunctor M M) M

  return = NaturalTransformation.transform returnNT
  join   = NaturalTransformation.transform joinNT

  field
    returnJoin : {X : Obj}    -> join X ∘ (return (act M X)) ≡ id
    mapReturnJoin : {X : Obj} -> join X ∘ fmap M (return X)  ≡ id
    joinJoin : {X : Obj} -> join X ∘ join (act M X) ≡ join X ∘ fmap M (join X)

  open Functor M public


---------------------------------------------------------------------------
-- The bind presentation of monads (optional)
---------------------------------------------------------------------------

module _ {C : Category} (M : Monad C) where

  open NaturalTransformation
  open Monad

  bind : ∀ {X Y} → Category.Hom C X (act M Y) -> Category.Hom C (act M X) (act M Y)
  bind f = join M _ ∘ fmap M f where open Category C

  bindReturn : ∀ {X} → bind (return M X) ≡ Category.id C
  bindReturn = mapReturnJoin M

  returnBind : ∀ {X Y}{f : Category.Hom C X (act M Y)}  → Category.comp C (return M _) (bind f) ≡ f
  returnBind {f = f} = C ⊧begin
    (< join M _ > ∘Syn fmapSyn (functor M) < f >) ∘Syn < return M _ >
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

  bindBind : ∀ {X Y Z}{f : Category.Hom C X (act M Y)}{g : Category.Hom C Y (act M Z)} →
             bind (Category.comp C f (bind g)) ≡ Category.comp C (bind f) (bind g)
  bindBind {f = f} {g} = C ⊧begin
    < join M _ > ∘Syn fmapSyn (functor M) ((< join M _ > ∘Syn fmapSyn (functor M) < g >) ∘Syn < f >)
      ≡⟦ solveCat refl ⟧
    -[ < join M _ > ∘Syn fmapSyn (functor M) < join M _ > ]- ∘Syn fmapSyn (functor M) (fmapSyn (functor M) < g >) ∘Syn fmapSyn (functor M) < f >
      ≡⟦ reduced (rq (sym (joinJoin M)) , rd , rd) ⟧
    -[ < join M _ > ∘Syn  < join M _ > ]- ∘Syn fmapSyn (functor M) (fmapSyn (functor M) < g >) ∘Syn fmapSyn (functor M) < f >
      ≡⟦ solveCat refl ⟧
    < join M _ > ∘Syn -[ < join M _ > ∘Syn fmapSyn (functor M) (fmapSyn (functor M) < g >) ]- ∘Syn fmapSyn (functor M) < f >
      ≡⟦ reduced (rd , rq (natural (joinNT M) _ _ g) , rd) ⟧
    < join M _ > ∘Syn -[ fmapSyn (functor M) < g > ∘Syn < join M _ > ]- ∘Syn fmapSyn (functor M) < f >
      ≡⟦ solveCat refl ⟧
    (< join M _ > ∘Syn fmapSyn (functor M) < g >) ∘Syn (< join M _ > ∘Syn fmapSyn (functor M) < f >)
      ⟦∎⟧

---------------------------------------------------------------------------
-- Hutton's Razor is a monad
---------------------------------------------------------------------------

module _ where

  open Monad
  open NaturalTransformation

  data Expr (X : Set) : Set where
    var : X -> Expr X
    num : ℕ -> Expr X
    _+E_ : Expr X -> Expr X -> Expr X

  mapExpr : {X Y : Set} -> (X -> Y) -> Expr X -> Expr Y
  mapExpr f (var x) = var (f x)
  mapExpr f (num x) = num x
  mapExpr f (e +E e') = mapExpr f e +E mapExpr f e'

  EXPR : Functor SET SET
  Functor.act EXPR = Expr
  Functor.fmap EXPR = mapExpr
  Functor.identity EXPR = ext lemma where
    lemma : {A : Set} -> (x : Expr A) → mapExpr (λ x₁ → x₁) x ≡ x
    lemma (var x) = refl
    lemma (num x) = refl
    lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')
  Functor.homomorphism EXPR {X} {f = f} {g} = ext lemma where
    lemma : (x : Expr X) → mapExpr (λ x₁ → g (f x₁)) x ≡ mapExpr g (mapExpr f x)
    lemma (var x) = refl
    lemma (num x) = refl
    lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')

  joinExpr : {X : Set} -> Expr (Expr X) -> Expr X
  joinExpr (var e) = e
  joinExpr (num x) = num x
  joinExpr (e +E e') = joinExpr e +E joinExpr e'

  EXPR-MONAD : Monad SET
  functor EXPR-MONAD = EXPR
  transform (returnNT EXPR-MONAD) X = var
  natural (returnNT EXPR-MONAD) X Y f = refl
  transform (joinNT EXPR-MONAD) X = joinExpr
  natural (joinNT EXPR-MONAD) X Y f = ext lemma where
    lemma : (x : Expr (Expr X)) → joinExpr (mapExpr (mapExpr f) x) ≡ mapExpr f (joinExpr x)
    lemma (var e) = refl
    lemma (num x) = refl
    lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')
  returnJoin EXPR-MONAD = refl
  mapReturnJoin EXPR-MONAD {X} = ext lemma where
    lemma : (x : Expr X) → joinExpr (mapExpr var x) ≡ x
    lemma (var x) = refl
    lemma (num x) = refl
    lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')
  joinJoin EXPR-MONAD {X} = ext lemma where
    lemma : (x : Expr (Expr (Expr X))) → joinExpr (joinExpr x) ≡ joinExpr (mapExpr joinExpr x)
    lemma (var e) = refl
    lemma (num x) = refl
    lemma (e +E e₁) = cong₂ _+E_ (lemma e) (lemma e₁)

  bindExpr : {X Y : Set} -> (X -> Expr Y) -> Expr X -> Expr Y
  bindExpr f = joinExpr ∘′ mapExpr f


---------------------------------------------------------------------------
-- Adding a bottom is a monad
---------------------------------------------------------------------------

module _ where

  open Preorder
  open MonotoneMap
  open Monad
  open NaturalTransformation

  data Lift (P : Set) : Set where
    η : P -> Lift P
    ⊥' : Lift P

  data Lift≤ (P : Preorder) : Lift (Carrier P) -> Lift (Carrier P) -> Set where
    η< : ∀ {p p'} → _≤_ P p p' -> Lift≤ P (η p) (η p')
    bottom : ∀ {x} → Lift≤ P ⊥' x

  Lift-reflexive : (P : Preorder) -> (x : Lift (Carrier P)) → Lift≤ P x x
  Lift-reflexive P (η p) = η< (reflexive P)
  Lift-reflexive P ⊥' = bottom

  Lift-transitive : (P : Preorder) -> {x y z : Lift (Carrier P)} →  Lift≤ P x y -> Lift≤ P y z -> Lift≤ P x z
  Lift-transitive P (η< p) (η< q) = η< (transitive P p q)
  Lift-transitive P bottom (η< p) = bottom
  Lift-transitive P bottom bottom = bottom

  mapLift : {X Y : Set} -> (f : X -> Y) -> Lift X -> Lift Y
  mapLift f (η x) = η (f x)
  mapLift f ⊥' = ⊥'

  LIFT : Functor PREORDER PREORDER
  Carrier (Functor.act LIFT P) = Lift (Carrier P)
  _≤_ (Functor.act LIFT P) = Lift≤ P
  reflexive (Functor.act LIFT P) = Lift-reflexive P _
  transitive (Functor.act LIFT P) = Lift-transitive P
  propositional (Functor.act LIFT P) (η< p) (η< q) = cong η< (propositional P p q)
  propositional (Functor.act LIFT P) bottom bottom = refl
  fun (Functor.fmap LIFT f) = mapLift (fun f)
  monotone (Functor.fmap LIFT f) .(η _) .(η _) (η< p) = η< (monotone f _ _ p)
  monotone (Functor.fmap LIFT f) .⊥' y bottom = bottom
  Functor.identity LIFT = eqMonotoneMap (ext λ { (η x) → refl ; ⊥' → refl })
  Functor.homomorphism LIFT = eqMonotoneMap (ext λ { (η x) → refl ; ⊥' → refl })

  LIFT-MONAD : Monad PREORDER
  functor LIFT-MONAD = LIFT
  fun (transform (returnNT LIFT-MONAD) P) = η
  monotone (transform (returnNT LIFT-MONAD) P) x y p = η< p
  natural (returnNT LIFT-MONAD) X Y f = eqMonotoneMap refl
  fun (transform (joinNT LIFT-MONAD) P) (η x) = x
  fun (transform (joinNT LIFT-MONAD) P) ⊥' = ⊥'
  monotone (transform (joinNT LIFT-MONAD) P) .(η _) .(η _) (η< p) = p
  monotone (transform (joinNT LIFT-MONAD) P) .⊥' y bottom = bottom
  natural (joinNT LIFT-MONAD) X Y f = eqMonotoneMap (ext λ { (η x) → refl ; ⊥' → refl })
  returnJoin LIFT-MONAD = eqMonotoneMap refl
  mapReturnJoin LIFT-MONAD = eqMonotoneMap (ext λ { (η x) → refl ; ⊥' → refl })
  joinJoin LIFT-MONAD = eqMonotoneMap (ext λ { (η x) → refl ; ⊥' → refl })

---------------------------------------------------------------------------
-- Now You Try: Lists are monads
---------------------------------------------------------------------------

module _ where

  open Monad
  open NaturalTransformation

  LIST : Functor SET SET
  Functor.act LIST = List
  Functor.fmap LIST = List.map
  Functor.identity LIST = ext map-id
  Functor.homomorphism LIST = ext map-compose

  concat-++ : ∀ {X} (xss yss : List (List X)) → concat (xss ++ yss) ≡ concat xss ++ concat yss
  concat-++ xss yss = {!!}

  LIST-MONAD : Monad SET
  functor LIST-MONAD = {!!}
  returnNT LIST-MONAD = {!!}
  joinNT LIST-MONAD = {!!}
  returnJoin LIST-MONAD = {!!}
  mapReturnJoin LIST-MONAD = {!!}
  joinJoin LIST-MONAD = {!!}

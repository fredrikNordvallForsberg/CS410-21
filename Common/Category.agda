{-# OPTIONS --type-in-type #-}
module Common.Category where

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs.WithK
import Function as Fun

----------------------------
-- Function extensionality
----------------------------

postulate
  ext : Extensionality _ _

----------------------------
-- Categories
----------------------------

record Category : Set where
  eta-equality
  infixr 9 _∘_

  field
    Obj : Set
    Hom : Obj -> Obj -> Set

  _⇒_ = Hom

  field
    id  : ∀ {A} → (A ⇒ A)
    comp : ∀ {A B C} → (A ⇒ B) → (B ⇒ C) → (A ⇒ C)

  _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
  f ∘ g = comp g f

  field
    assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C}{h : C ⇒ D} →
                (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f

----------------------------
-- Functors
----------------------------

record Functor (C D : Category) : Set where
  eta-equality
  private
    module C = Category C
    module D = Category D

  field
    act : C.Obj → D.Obj
    fmap : ∀ {A B} (f : A C.⇒ B) → act A D.⇒ act B

  field -- laws
    identity     : ∀ {A} → fmap (C.id {A}) ≡ D.id
    homomorphism : ∀ {X Y Z} {f : X C.⇒ Y}{g : Y C.⇒ Z} →
                   fmap (g C.∘ f) ≡ fmap g D.∘ fmap f
open Functor

idFunctor : {C : Category} -> Functor C C
act idFunctor X = X
fmap idFunctor f = f
identity idFunctor = refl
homomorphism idFunctor = refl

compFunctor : {A B C : Category} -> Functor A B → Functor B C → Functor A C
act (compFunctor F G) =  (act G) Fun.∘′ (act F)
fmap (compFunctor F G) f = fmap G (fmap F f)
identity (compFunctor F G) = trans (cong (fmap G) (identity F)) (identity G)
homomorphism (compFunctor F G) = trans (cong (fmap G) (homomorphism F)) (homomorphism G)

----------------------------
-- Natural transformations
----------------------------

record NaturalTransformation {C D : Category}
                             (F G : Functor C D) : Set where
  eta-equality
  private
    module F = Functor F
    module G = Functor G
    module C = Category C
    module D = Category D

  field
    transform   : ∀ X → F.act X D.⇒ G.act X
    natural     : ∀ X Y (f : X C.⇒ Y ) →
                  transform Y D.∘ F.fmap f ≡ G.fmap f D.∘ transform X
open NaturalTransformation

eqNatTrans : {C D : Category}{F G : Functor C D} ->
             (η ρ : NaturalTransformation F G) ->
             ((X : Category.Obj C) -> transform η X ≡ transform ρ X) ->
             η ≡ ρ
eqNatTrans {C} η ρ p with ext p
... | refl = eqNatTrans' η ρ refl (ext λ X → ext λ Y → ext λ f → uip _ _) where
  eqNatTrans' : {C D : Category}{F G : Functor C D} ->
                (η ρ : NaturalTransformation F G) ->
                (p : transform η ≡ transform ρ) ->
                subst (λ z → (X Y : Category.Obj C)(f : Category.Hom C X Y) → Category.comp D (fmap F f) (z Y) ≡ Category.comp D (z X) (fmap G f)) p (natural η) ≡ (natural ρ) ->
               η ≡ ρ
  eqNatTrans' η ρ refl refl = refl

----------------------------
-- Monads
----------------------------

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

----------------------------
-- The category of Sets
----------------------------

SET : Category
Category.Obj SET = Set
Category.Hom SET A B = A -> B
Category.id SET = Fun.id
Category.comp SET f g = g Fun.∘′ f
Category.assoc SET = refl
Category.identityˡ SET = refl
Category.identityʳ SET = refl

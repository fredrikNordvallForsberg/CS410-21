{-# OPTIONS --type-in-type #-}
module NowYouTry.Categories where

open import Data.Unit hiding (_≤_)
open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality
open import Axiom.UniquenessOfIdentityProofs.WithK

open import Common.Category

open Category

---------------------------------------------------------------------------
-- Monoids and monoid morphisms
---------------------------------------------------------------------------

record Monoid : Set₁ where
  field
    Carrier : Set
    _∙_ : Carrier -> Carrier -> Carrier
    ε : Carrier

  field
    assoc : ∀ {x y z} → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z
    identityˡ : ∀ {x} → ε ∙ x ≡ x
    identityʳ : ∀ {x} → x ∙ ε ≡ x
open Monoid

record MonoidMorphism (A B : Monoid) : Set where
  private
    module A = Monoid A
    module B = Monoid B

  field
    fun : Carrier A -> Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-∙ : ∀ x y → fun (x A.∙ y) ≡ (fun x B.∙ fun y)
open MonoidMorphism

eqMonoidMorphism : {A B : Monoid} -> {f g : MonoidMorphism A B} ->
                   fun f ≡ fun g -> f ≡ g
eqMonoidMorphism {A} {B} {f} {g} refl =
  eqMonoidMorphism' (ext (λ x → ext λ y → uip _ _)) (uip _ _)
  where
    module A = Monoid A
    module B = Monoid B
    eqMonoidMorphism' : {fun : A.Carrier -> B.Carrier}
                        {∙-f ∙-g : ∀ x y → fun (x A.∙ y) ≡ (fun x B.∙ fun y)}
                        {ε-f ε-g : fun (A.ε) ≡ B.ε} ->
                        ∙-f ≡ ∙-g -> ε-f ≡ ε-g ->
                        _≡_ {A = MonoidMorphism A B}
                            (record { fun = fun ; preserves-∙ = ∙-f ; preserves-ε = ε-f })
                            (record { fun = fun ; preserves-∙ = ∙-g ; preserves-ε = ε-g })
    eqMonoidMorphism' refl refl = refl

MONOID : Category
Obj MONOID = Monoid
Hom MONOID = MonoidMorphism
fun (Category.id MONOID) = λ x → x
preserves-ε (Category.id MONOID) = refl
preserves-∙ (Category.id MONOID) x y = refl
fun (comp MONOID f g) = comp SET (fun f) (fun g)
preserves-ε (comp MONOID f g) = trans (cong (fun g) (preserves-ε f)) (preserves-ε g)
preserves-∙ (comp MONOID {A} {B} {C} f g) x y = begin
  fun g (fun f (x A.∙ y))
    ≡⟨ cong (fun g) (preserves-∙ f x y) ⟩
  fun g (fun f x B.∙ fun f y)
    ≡⟨ preserves-∙ g _ _ ⟩
  (fun g (fun f x) C.∙ fun g (fun f y)) ∎ where
         module A = Monoid A
         module B = Monoid B
         module C = Monoid C
         open ≡-Reasoning
assoc MONOID = eqMonoidMorphism refl
identityˡ MONOID = eqMonoidMorphism refl
identityʳ MONOID = eqMonoidMorphism refl

---------------------------------------------------------------------------
-- Discrete categories
---------------------------------------------------------------------------

discrete : Set -> Category
Obj (discrete X) = X
Hom (discrete X) x y = x ≡ y
Category.id (discrete X) = refl
comp (discrete X) p q = trans p q
assoc (discrete X) = uip _ _
identityˡ (discrete X) = uip _ _
identityʳ (discrete X) = uip _ _

---------------------------------------------------------------------------
-- Monoids as categories
---------------------------------------------------------------------------

monoid : Monoid -> Category
Obj (monoid M) = ⊤
Hom (monoid M) _ _ = Carrier M
Category.id (monoid M) = ε M
comp (monoid M) = _∙_ M
assoc (monoid M) = assoc M
identityˡ (monoid M) = identityʳ M
identityʳ (monoid M) = identityˡ M

---------------------------------------------------------------------------
-- Preorders as categories
---------------------------------------------------------------------------

record Preorder : Set1 where
  field
    Carrier : Set
    _≤_ : Carrier -> Carrier -> Set
    reflexive : ∀ {x} → x ≤ x
    transitive : ∀ {x y z} → x ≤ y -> y ≤ z -> x ≤ z
    propositional : ∀ {x y} → (p q : x ≤ y) -> p ≡ q

open Preorder

porder : Preorder -> Category
Obj (porder P) = Carrier P
Hom (porder P) x y = _≤_ P x y
Category.id (porder P) = reflexive P
comp (porder P) = transitive P
assoc (porder P) = propositional P _ _
identityˡ (porder P) = propositional P _ _
identityʳ (porder P) = propositional P _ _

---------------------------------------------------------------------------
-- Now You Try
---------------------------------------------------------------------------

record MonotoneMap (P Q : Preorder) : Set1 where
  private
    module P = Preorder P
    module Q = Preorder Q

  field
    fun : Carrier P -> Carrier Q
    monotone : ∀ x y → x P.≤ y -> fun x Q.≤ fun y
open MonotoneMap

eqMonotoneMap : {P Q : Preorder} -> {f g : MonotoneMap P Q} ->
                   fun f ≡ fun g -> f ≡ g
eqMonotoneMap {P} {Q} {f} {g} refl = cong (λ z → record { fun = fun g; monotone = z })
                                          (ext λ x → ext (λ y → ext λ p → propositional Q _ _))

PREORDER : Category
PREORDER = ?

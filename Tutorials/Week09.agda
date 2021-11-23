{-# OPTIONS --type-in-type --prop #-}
module Tutorials.Week09 where

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Common.Category
open import Lectures.Adjunctions

open Category
open Functor
open NaturalTransformation
open Adjunction

-- The first toy example

data Obj1 : Set where
  A B C : Obj1

data Hom1 : Obj1 → Obj1 → Set where
  ac : Hom1 A C
  bc : Hom1 B C
  Id : (X : Obj1) → Hom1 X X

C1 : Category
Obj C1 = Obj1
Hom C1 = Hom1
id C1 = Id _
comp C1 (Id _) g = g
comp C1 f (Id _) = f
------------------------------------------------
assoc C1 {f = ac} {Id .C} {Id .C} = refl
assoc C1 {f = bc} {Id .C} {Id .C} = refl
assoc C1 {f = Id .A} {ac} {Id .C} = refl
assoc C1 {f = Id .B} {bc} {Id .C} = refl
assoc C1 {f = Id .A} {Id .A} {ac} = refl
assoc C1 {f = Id .B} {Id .B} {bc} = refl
assoc C1 {f = Id _} {Id _} {Id _} = refl
identityˡ C1 {f = ac} = refl
identityˡ C1 {f = bc} = refl
identityˡ C1 {f = Id _} = refl
identityʳ C1 = refl

data Obj2 : Set where
  AA AB AC BA BB BC CA CB CC : Obj2

data Hom2 : Obj2 → Obj2 → Set where
  aa : Hom2 AA CC
  ab : Hom2 AB CC
  ac : Hom2 AC CC
  ba : Hom2 BA CC
  bb : Hom2 BB CC
  bc : Hom2 BC CC
  ca : Hom2 CA CC
  cb : Hom2 CB CC
  Id : (X : Obj2) → Hom2 X X

C2 : Category
Obj C2 = Obj2
Hom C2 = Hom2
id C2 = Id _
comp C2 (Id _) g = g
comp C2 f (Id _) = f
------------------------------------------------
assoc C2 {f = aa} {Id .CC} {Id .CC} = refl
assoc C2 {f = ab} {Id .CC} {Id .CC} = refl
assoc C2 {f = ac} {Id .CC} {Id .CC} = refl
assoc C2 {f = ba} {Id .CC} {Id .CC} = refl
assoc C2 {f = bb} {Id .CC} {Id .CC} = refl
assoc C2 {f = bc} {Id .CC} {Id .CC} = refl
assoc C2 {f = ca} {Id .CC} {Id .CC} = refl
assoc C2 {f = cb} {Id .CC} {Id .CC} = refl
assoc C2 {f = Id .AA} {aa} {Id .CC} = refl
assoc C2 {f = Id .AB} {ab} {Id .CC} = refl
assoc C2 {f = Id .AC} {ac} {Id .CC} = refl
assoc C2 {f = Id .BA} {ba} {Id .CC} = refl
assoc C2 {f = Id .BB} {bb} {Id .CC} = refl
assoc C2 {f = Id .BC} {bc} {Id .CC} = refl
assoc C2 {f = Id .CA} {ca} {Id .CC} = refl
assoc C2 {f = Id .CB} {cb} {Id .CC} = refl
assoc C2 {f = Id .AA} {Id .AA} {aa} = refl
assoc C2 {f = Id .AB} {Id .AB} {ab} = refl
assoc C2 {f = Id .AC} {Id .AC} {ac} = refl
assoc C2 {f = Id .BA} {Id .BA} {ba} = refl
assoc C2 {f = Id .BB} {Id .BB} {bb} = refl
assoc C2 {f = Id .BC} {Id .BC} {bc} = refl
assoc C2 {f = Id .CA} {Id .CA} {ca} = refl
assoc C2 {f = Id .CB} {Id .CB} {cb} = refl
assoc C2 {f = Id _} {Id _} {Id _} = refl
identityˡ C2 {f = aa} = refl
identityˡ C2 {f = ab} = refl
identityˡ C2 {f = ac} = refl
identityˡ C2 {f = ba} = refl
identityˡ C2 {f = bb} = refl
identityˡ C2 {f = bc} = refl
identityˡ C2 {f = ca} = refl
identityˡ C2 {f = cb} = refl
identityˡ C2 {f = Id _} = refl
identityʳ C2 = refl

F : Functor C1 C2
act F A = AA
act F B = CB
act F C = CC
fmap F ac = aa
fmap F bc = cb
fmap F (Id _) = Id _
identity F = refl
homomorphism F {f = ac} {Id .C} = refl
homomorphism F {f = bc} {Id .C} = refl
homomorphism F {f = Id .A} {ac} = refl
homomorphism F {f = Id .B} {bc} = refl
homomorphism F {f = Id _} {Id _} = refl

G : Functor C2 C1
act G AA = A
act G CB = B
act G X = C
fmap G aa = ac
fmap G cb = bc
fmap G ab = Id _
fmap G ac = Id _
fmap G ba = Id _
fmap G bb = Id _
fmap G bc = Id _
fmap G ca = Id _
fmap G (Id _) = Id _
identity G = refl
homomorphism G {f = aa} {Id .CC} = refl
homomorphism G {f = ab} {Id .CC} = refl
homomorphism G {f = ac} {Id .CC} = refl
homomorphism G {f = ba} {Id .CC} = refl
homomorphism G {f = bb} {Id .CC} = refl
homomorphism G {f = bc} {Id .CC} = refl
homomorphism G {f = ca} {Id .CC} = refl
homomorphism G {f = cb} {Id .CC} = refl
homomorphism G {f = Id .AA} {aa} = refl
homomorphism G {f = Id .AB} {ab} = refl
homomorphism G {f = Id .AC} {ac} = refl
homomorphism G {f = Id .BA} {ba} = refl
homomorphism G {f = Id .BB} {bb} = refl
homomorphism G {f = Id .BC} {bc} = refl
homomorphism G {f = Id .CA} {ca} = refl
homomorphism G {f = Id .CB} {cb} = refl
homomorphism G {f = Id _} {Id _} = refl

adj : Adjunction G F
to adj {AA} ac = aa
to adj {AA} (Id .(act G AA)) = Id _
to adj {AB} (Id .(act G AB)) = ab
to adj {AC} (Id .(act G AC)) = ac
to adj {BA} (Id .(act G BA)) = ba
to adj {BB} (Id .(act G BB)) = bb
to adj {BC} (Id .(act G BC)) = bc
to adj {CA} (Id .(act G CA)) = ca
to adj {CB} bc = cb
to adj {CB} (Id .(act G CB)) = Id _
to adj {CC} (Id .(act G CC)) = Id _
from adj {B = A} (Id .(act F A)) = Id _
from adj {B = B} (Id .(act F B)) = Id _
from adj {B = C} aa = ac
from adj {B = C} ab = Id _
from adj {B = C} ac = Id _
from adj {B = C} ba = Id _
from adj {B = C} bb = Id _
from adj {B = C} bc = Id _
from adj {B = C} ca = Id _
from adj {B = C} cb = bc
from adj {B = C} (Id .(act F C)) = Id _
left-inverse-of adj {AA} ac = refl
left-inverse-of adj {AA} (Id .(act G AA)) = refl
left-inverse-of adj {AB} (Id .(act G AB)) = refl
left-inverse-of adj {AC} (Id .(act G AC)) = refl
left-inverse-of adj {BA} (Id .(act G BA)) = refl
left-inverse-of adj {BB} (Id .(act G BB)) = refl
left-inverse-of adj {BC} (Id .(act G BC)) = refl
left-inverse-of adj {CA} (Id .(act G CA)) = refl
left-inverse-of adj {CB} bc = refl
left-inverse-of adj {CB} (Id .(act G CB)) = refl
left-inverse-of adj {CC} (Id .(act G CC)) = refl
right-inverse-of adj {B = A} (Id .(act F A)) = refl
right-inverse-of adj {B = B} (Id .(act F B)) = refl
right-inverse-of adj {B = C} aa = refl
right-inverse-of adj {B = C} ab = refl
right-inverse-of adj {B = C} ac = refl
right-inverse-of adj {B = C} ba = refl
right-inverse-of adj {B = C} bb = refl
right-inverse-of adj {B = C} bc = refl
right-inverse-of adj {B = C} ca = refl
right-inverse-of adj {B = C} cb = refl
right-inverse-of adj {B = C} (Id .(act F C)) = refl
to-natural adj {X} {X'} {B₁} {B'} f g = ext (lemma {B₁} {B'} {X} {X'} g f) where
  lemma : {B₁ B' : Obj1}{X X' : Obj2} → (g : Hom1 B₁ B')(f : Hom2 X' X) →
           ∀ x → comp C2 f (comp C2 (to adj x) (fmap F g)) ≡ to adj (comp C1 (fmap G f) (comp C1 x g))
  lemma {.A} {.C} {AA} {.AA} ac (Id .AA) (Id .A) = refl
  lemma {.B} {.C} {AA} {.AA} bc (Id .AA) ()
  lemma {.C} {.C} {AA} {.AA} (Id .C) (Id .AA) ac = refl
  lemma {.(act G AA)} {.(act G AA)} {AA} {.AA} (Id .(act G AA)) (Id .AA) (Id .(act G AA)) = refl
  lemma {.A} {.C} {AB} {.AB} ac (Id .AB) ()
  lemma {.B} {.C} {AB} {.AB} bc (Id .AB) ()
  lemma {.(act G AB)} {.(act G AB)} {AB} {.AB} (Id .(act G AB)) (Id .AB) (Id .(act G AB)) = refl
  lemma {.A} {.C} {AC} {.AC} ac (Id .AC) ()
  lemma {.B} {.C} {AC} {.AC} bc (Id .AC) ()
  lemma {.(act G AC)} {.(act G AC)} {AC} {.AC} (Id .(act G AC)) (Id .AC) (Id .(act G AC)) = refl
  lemma {.A} {.C} {BA} {.BA} ac (Id .BA) ()
  lemma {.B} {.C} {BA} {.BA} bc (Id .BA) ()
  lemma {.(act G BA)} {.(act G BA)} {BA} {.BA} (Id .(act G BA)) (Id .BA) (Id .(act G BA)) = refl
  lemma {.A} {.C} {BB} {.BB} ac (Id .BB) ()
  lemma {.B} {.C} {BB} {.BB} bc (Id .BB) ()
  lemma {.(act G BB)} {.(act G BB)} {BB} {.BB} (Id .(act G BB)) (Id .BB) (Id .(act G BB)) = refl
  lemma {.A} {.C} {BC} {.BC} ac (Id .BC) ()
  lemma {.B} {.C} {BC} {.BC} bc (Id .BC) ()
  lemma {.(act G BC)} {.(act G BC)} {BC} {.BC} (Id .(act G BC)) (Id .BC) (Id .(act G BC)) = refl
  lemma {.A} {.C} {CA} {.CA} ac (Id .CA) ()
  lemma {.B} {.C} {CA} {.CA} bc (Id .CA) ()
  lemma {.(act G CA)} {.(act G CA)} {CA} {.CA} (Id .(act G CA)) (Id .CA) (Id .(act G CA)) = refl
  lemma {.A} {.C} {CB} {.CB} ac (Id .CB) ()
  lemma {.B} {.C} {CB} {.CB} bc (Id .CB) (Id .B) = refl
  lemma {.C} {.C} {CB} {.CB} (Id .C) (Id .CB) bc = refl
  lemma {.(act G CB)} {.(act G CB)} {CB} {.CB} (Id .(act G CB)) (Id .CB) (Id .(act G CB)) = refl
  lemma {.A} {.C} {CC} {.AA} ac aa ()
  lemma {.A} {.C} {CC} {.AB} ac ab ()
  lemma {.A} {.C} {CC} {.AC} ac ac ()
  lemma {.A} {.C} {CC} {.BA} ac ba ()
  lemma {.A} {.C} {CC} {.BB} ac bb ()
  lemma {.A} {.C} {CC} {.BC} ac bc ()
  lemma {.A} {.C} {CC} {.CA} ac ca ()
  lemma {.A} {.C} {CC} {.CB} ac cb ()
  lemma {.A} {.C} {CC} {.CC} ac (Id .CC) ()
  lemma {.B} {.C} {CC} {.AA} bc aa ()
  lemma {.B} {.C} {CC} {.AB} bc ab ()
  lemma {.B} {.C} {CC} {.AC} bc ac ()
  lemma {.B} {.C} {CC} {.BA} bc ba ()
  lemma {.B} {.C} {CC} {.BB} bc bb ()
  lemma {.B} {.C} {CC} {.BC} bc bc ()
  lemma {.B} {.C} {CC} {.CA} bc ca ()
  lemma {.B} {.C} {CC} {.CB} bc cb ()
  lemma {.B} {.C} {CC} {.CC} bc (Id .CC) ()
  lemma {.(act G CC)} {.(act G CC)} {CC} {.AA} (Id .(act G CC)) aa (Id .(act G CC)) = refl
  lemma {.(act G CC)} {.(act G CC)} {CC} {.AB} (Id .(act G CC)) ab (Id .(act G CC)) = refl
  lemma {.(act G CC)} {.(act G CC)} {CC} {.AC} (Id .(act G CC)) ac (Id .(act G CC)) = refl
  lemma {.(act G CC)} {.(act G CC)} {CC} {.BA} (Id .(act G CC)) ba (Id .(act G CC)) = refl
  lemma {.(act G CC)} {.(act G CC)} {CC} {.BB} (Id .(act G CC)) bb (Id .(act G CC)) = refl
  lemma {.(act G CC)} {.(act G CC)} {CC} {.BC} (Id .(act G CC)) bc (Id .(act G CC)) = refl
  lemma {.(act G CC)} {.(act G CC)} {CC} {.CA} (Id .(act G CC)) ca (Id .(act G CC)) = refl
  lemma {.(act G CC)} {.(act G CC)} {CC} {.CB} (Id .(act G CC)) cb (Id .(act G CC)) = refl
  lemma {.(act G CC)} {.(act G CC)} {CC} {.CC} (Id .(act G CC)) (Id .CC) (Id .(act G CC)) = refl



-- Another example: the relationship between reflexive and arbitrary relations

-- For simplicity, we use the `Prop` universe of Agda; if P : Prop,
-- then automatically x = y whenever x, y : P. Here is how we can
-- package up a Prop as a Set:

record Prf (P : Prop) : Set where
  constructor prf
  field
    prop : P
open Prf

-- And this packaging up is functorial:

Prf-map : {P Q : Prop} → (P → Q) → Prf P → Prf Q
Prf-map f (prf p) = prf (f p)

-- Category of relations
Rel : Category
Obj Rel = Σ[ X ∈ Set ] (X → X → Prop)
-- Morphisms are functions which preserve the relation
Hom Rel (X , R) (Y , S) =
  Σ[ f ∈ (X → Y) ] (∀ x x' → Prf (R x x') → Prf (S (f x) (f x')))
id Rel = (λ x → x) , λ x x' r → r
comp Rel (f , f') (g , g') = (λ x → g (f x)) , λ x x' r → g' _ _ (f' x x' r)
assoc Rel = refl
identityˡ Rel = refl
identityʳ Rel = refl

-- Category of reflexive relations: for each x, we must have a proof of `R x x`
ReflRel : Category
Obj ReflRel = Σ[ X ∈ Set ] Σ[ R ∈ (X → X → Prop) ] (∀ x → Prf (R x x))
-- Morphisms are the same as above
Hom ReflRel (X , R , r) (Y , S , s) =
  Σ[ f ∈ (X → Y) ] (∀ x x' → Prf (R x x') → Prf (S (f x) (f x')))
id ReflRel = (λ x → x) , λ x x' r → r
comp ReflRel (f , f') (g , g') = (λ x → g (f x)) , λ x x' r → g' _ _ (f' x x' r)
assoc ReflRel = refl
identityˡ ReflRel = refl
identityʳ ReflRel = refl

-- We can forget that a relation is reflexive; this is a functor
Forget : Functor ReflRel Rel
act Forget (X , R , r)= (X , R)
fmap Forget f = f
identity Forget = refl
homomorphism Forget = refl

-- We can also restrict the relation to the elements where it happens
-- to be reflexive; this turns an arbitrary relation into a reflexive
-- one
Restrict : Functor Rel ReflRel
-- We only keep the x ∈ X where there is a proof of `R x x`; the relation stays the same
act Restrict (X , R) =
  ((Σ[ x ∈ X ] Prf (R x x)) , (λ (x , _) (x' , _) → R x x') , λ (x , r) → r)
-- Since morphisms preserve relations, a given morphism in `Rel` can
-- be made a morphism in ReflRel too
fmap Restrict (f , f') = ((λ (x , r) → (f x , f' x x r)) ,
                          (λ (x , _) (x' , _) → f' x x'))
identity Restrict = refl
homomorphism Restrict = refl

-- This forms an adjunction (think about why!)
Forget⊣Restrict : Adjunction Forget Restrict
to Forget⊣Restrict {X , R , r} {Y , S} (f , f')
  = ((λ x → (f x , f' x x (r x))) , f')
from Forget⊣Restrict {X , R , r} {Y , S} (f , f')
  = ((λ x → proj₁ (f x)) , f')
left-inverse-of Forget⊣Restrict h = refl
right-inverse-of Forget⊣Restrict {X , R , r} {Y , S} (f , f') = refl
to-natural Forget⊣Restrict f g = refl

-- Alternatively, we could enlarge a given relation to make it reflexive

-- Here is the disjoint union and equality, but for `Prop`s; we can
-- use this to add a new proof that any two equal elements are related
data _∨_ (P Q : Prop) : Prop where
  inl : P → P ∨ Q
  inr : Q → P ∨ Q

data _≡'_ {A : Set}(a : A) : A → Prop where
  refl : a ≡' a

Enlarge : Functor Rel ReflRel
-- We make a new relation, which holds if the old relation holds, or if x = x'
act Enlarge (X , R) = X , (λ x x' → R x x' ∨ (x ≡' x')) , λ x → prf (inr refl)
fmap Enlarge (f , f') = (f , λ { x x' → Prf-map λ { (inl r) → inl (prop (f' x x' (prf r))) ; (inr refl) → inr refl } })
identity Enlarge = refl
homomorphism Enlarge = refl

-- This again forms an adjunction (again: think why!)
Enlarge⊣Forget : Adjunction Enlarge Forget
to Enlarge⊣Forget (f , f') = (f , λ x x' q → f' x x' (Prf-map inl q))
from Enlarge⊣Forget {B = X , R , r} (f , f')
 = (f , λ x x' q → (Prf-map (λ { (inl y) → prop (f' x x' (prf y)) ; (inr refl) → prop (r (f x)) }) q))
left-inverse-of Enlarge⊣Forget h = refl
right-inverse-of Enlarge⊣Forget h = refl
to-natural Enlarge⊣Forget f g = refl

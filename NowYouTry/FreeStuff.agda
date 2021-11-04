{-# OPTIONS --type-in-type #-}
module NowYouTry.FreeStuff where

open import Axiom.UniquenessOfIdentityProofs.WithK
open import Data.List as List
open import Data.List.Properties
  using (++-assoc; ++-identityʳ; map-++-commute; map-id; map-compose)
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Empty

open import Lectures.Categories
open import Lectures.FunctorsAndNatTransformations
open import Lectures.Adjunctions

open import Common.Category
open import Common.Category.Solver

---------------------------------------------------------------------------
-- Free monoids
---------------------------------------------------------------------------

open Functor
open NaturalTransformation
open Adjunction

module _ where

  open Monoid
  open MonoidMorphism

  freeMonoid : Functor SET MONOID
  Carrier (act freeMonoid X) = List X
  _∙_ (act freeMonoid X) = _++_
  ε (act freeMonoid X) = []
  assoc (act freeMonoid X) {xs} {ys} {zs} = sym (++-assoc xs ys zs)
  identityˡ (act freeMonoid X) = refl
  identityʳ (act freeMonoid X) = ++-identityʳ _
  fun (fmap freeMonoid f) = List.map f
  preserves-ε (fmap freeMonoid f) = refl
  preserves-∙ (fmap freeMonoid f) xs ys = map-++-commute f xs ys
  identity freeMonoid = eqMonoidMorphism (ext map-id)
  homomorphism freeMonoid = eqMonoidMorphism (ext map-compose)

module _ where

  open MonoidMorphism

  fold : {X : Set} -> (B : Monoid) -> (X -> Monoid.Carrier B) -> List X -> Monoid.Carrier B
  fold B g [] = Monoid.ε B
  fold B g (x ∷ xs) = g x ∙ fold B g xs where open Monoid B

  freeMonoidisFree : Adjunction freeMonoid forgetMonoid
  to freeMonoidisFree h x = fun h List.[ x ]
  fun (from freeMonoidisFree {B = B} f) = fold B f
  preserves-ε (from freeMonoidisFree f) = refl
  preserves-∙ (from freeMonoidisFree {B = B} f) [] ys = sym identityˡ where open Monoid B
  preserves-∙ (from freeMonoidisFree {B = B} f) (x ∷ xs) ys =
    trans (cong (f x ∙_) (preserves-∙ (from freeMonoidisFree {B = B} f) xs ys)) assoc  where open Monoid B
  left-inverse-of freeMonoidisFree {X} {B} h = eqMonoidMorphism (ext lemma) where
    lemma : (xs : List X) → fold B (λ x₁ → fun h (x₁ ∷ [])) xs ≡ fun h xs
    lemma [] = sym (preserves-ε h)
    lemma (x ∷ xs) = trans (cong (fun h (x ∷ []) ∙_) (lemma xs)) (sym (preserves-∙ h List.[ x ] xs)) where open Monoid B
  right-inverse-of freeMonoidisFree {B = B} k = ext λ x → identityʳ  where open Monoid B
  to-natural freeMonoidisFree f g = refl


---------------------------------------------------------------------------
-- Free categories
---------------------------------------------------------------------------

open Category

REL : Category
Obj REL = Σ[ A ∈ Set ] (A -> A -> Set)
Hom REL (A , R) (A' , R') = Σ[ f ∈ (A -> A') ] (∀ a b → R a b -> R' (f a) (f b))
id REL = id SET , λ a b r → r
comp REL (f , p) (f' , p') = comp SET f f' , λ a b r → p' _ _ (p _ _ r)
assoc REL = refl
identityˡ REL = refl
identityʳ REL = refl

forgetCategory : Functor CAT REL
act forgetCategory C = Obj C , Hom C
fmap forgetCategory F = act F , λ a b → fmap F
identity forgetCategory = refl
homomorphism forgetCategory = refl

data Star {A : Set}(R : A -> A -> Set) : A -> A -> Set where
  ε : ∀ {a} → Star R a a
  _∷_ : ∀ {a b c} → R a b -> Star R b c -> Star R a c

_++S_ : {A : Set}{R : A -> A -> Set} -> {a b c  : A} -> Star R a b -> Star R b c -> Star R a c
ε ++S ys = ys
(x ∷ xs) ++S ys = x ∷ (xs ++S ys)

assocS : {A : Set}{R : A -> A -> Set} ->
         {a b c d : A}(f : Star R a b)(g : Star R b c)(h : Star R c d) ->
         f ++S (g ++S h) ≡ (f ++S g) ++S h
assocS ε g h = refl
assocS (x ∷ f) g h = cong (x ∷_) (assocS f g h)

++S-identityˡ : {A : Set}{R : A -> A -> Set}{a b : A}(f : Star R a b) → f ++S ε ≡ f
++S-identityˡ ε = refl
++S-identityˡ (x ∷ f) = cong (x ∷_) (++S-identityˡ f)

mapS : {A B : Set}{R : A -> A -> Set}{Q : B -> B -> Set} ->
       (f : A -> B)(p : ∀ a a' → R a a' -> Q (f a) (f a')) ->
       {a a' : A} -> Star R a a' -> Star Q (f a) (f a')
mapS f p ε = ε
mapS f p (x ∷ r) = p _ _ x ∷ mapS f p r

mapS-++ : {A B : Set}{R : A -> A -> Set}{Q : B -> B -> Set} ->
          (f : A -> B)(p : ∀ a a' → R a a' -> Q (f a) (f a')) ->
          {a b c : A} -> (xs : Star R a b)(ys : Star R b c) ->
          mapS {Q = Q} f p (xs ++S ys) ≡ mapS f p xs ++S mapS f p ys
mapS-++ f p ε ys = refl
mapS-++ f p (x ∷ xs) ys = cong (_ ∷_) (mapS-++ f p xs ys)

mapS-id : ∀ {A R}{a b : A}(xs : Star R a b) -> mapS (id SET) (λ a b r → r) xs ≡ xs
mapS-id ε = refl
mapS-id (x ∷ xs) = cong (_ ∷_) (mapS-id xs)

mapS-∘ : {A A' A'' : Set}{R : A -> A -> Set}{R' : A' -> A' -> Set}{R'' : A'' -> A'' -> Set} ->
         (f : A -> A')(p : ∀ a a' → R a a' -> R' (f a) (f a')) ->
         (f' : A' -> A'')(p' : ∀ a a' → R' a a' -> R'' (f' a) (f' a')) ->
         {a b : A} -> (xs : Star R a b) ->
         mapS {Q = R''} (comp SET f f') (λ a b r → p' _ _ (p _ _ r)) xs ≡ mapS f' p' (mapS f p xs)
mapS-∘ f p f' p' ε = refl
mapS-∘ f p f' p' (x ∷ xs) = cong (_ ∷_) (mapS-∘ f p f' p' xs)

freeCategory : Functor REL CAT
Obj (act freeCategory (A , R)) = A
Hom (act freeCategory (A , R)) = Star R
id (act freeCategory (A , R)) = ε
comp (act freeCategory (A , R)) = _++S_
assoc (act freeCategory (A , R)) {f = f} {g} {h} = assocS f g h
identityˡ (act freeCategory (A , R)) = ++S-identityˡ _
identityʳ (act freeCategory (A , R)) = refl
act (fmap freeCategory (f , p)) = f
fmap (fmap freeCategory (f , p)) = mapS f p
identity (fmap freeCategory (f , p)) = refl
homomorphism (fmap freeCategory (f , p)) {f = xs} {ys} = mapS-++ f p xs ys
identity freeCategory = eqFunctor refl (ext mapS-id)
homomorphism freeCategory = eqFunctor refl (ext (mapS-∘ _ _ _ _))

foldStar : ∀ {A R a b} → (B : Category) ->
           (f : A -> Obj B)(p : ∀ a a' → R a a' -> Hom B (f a) (f a')) -> Star R a b -> Hom B (f a) (f b)
foldStar B f p ε = id B
foldStar B f p (x ∷ xs) = comp B (p _ _ x) (foldStar B f p xs)

freeCatisFree : Adjunction freeCategory forgetCategory
to freeCatisFree F = act F , λ a b r → fmap F (r ∷ ε)
act (from freeCatisFree (f , p)) = f
fmap (from freeCatisFree {B = B} (f , p)) xs = foldStar B f p xs
identity (from freeCatisFree (f , p)) = refl
homomorphism (from freeCatisFree {B = B} (f , p)) {f = ε} = sym (identityʳ B)
homomorphism (from freeCatisFree {B = B} (f , p)) {f = x ∷ xs} =
  trans (cong (comp B (p _ _ x)) (homomorphism (from freeCatisFree (f , p)) {f = xs})) (assoc B)
left-inverse-of freeCatisFree {A , R} {B = B} H = eqFunctor refl (ext lemma) where
  lemma : ∀ {a b} → (xs : Star R a b) -> foldStar B (act H) (λ _ _ f → fmap H (f ∷ ε)) xs ≡ fmap H xs
  lemma ε = sym (identity H)
  lemma (x ∷ xs) = trans (cong (comp B (fmap H (x ∷ ε))) (lemma xs)) (sym (homomorphism H))
right-inverse-of freeCatisFree {B = B} (f , p) = cong (f ,_) (ext λ a → ext (λ b → ext λ r → identityˡ B))
to-natural freeCatisFree f g = refl

---------------------------------------------------------------------------
-- Free monads
---------------------------------------------------------------------------


module _ (F : Functor SET SET) where
{-
  data FreeM (X : Set) : Set where
    return : X -> FreeM X
    layer : act F X -> FreeM X

  FMF : Functor SET SET
  act FMF = FreeM
  fmap FMF f (return x) = return (f x)
  fmap FMF f (layer x) = layer (fmap F f x)
  identity FMF = ext λ { (return x) → refl ; (layer x) → cong layer (cong-app (identity F) x) }
  homomorphism FMF = ext λ { (return x) → refl ; (layer x) → cong layer (cong-app (homomorphism F) x) }

  join : ∀ {X} → FreeM (FreeM X) -> FreeM X
  join (return x) = x
  join (layer x) = layer (fmap F {!!} x) -- STUCK HERE
-}

{-
  {-# NO_POSITIVITY_CHECK #-} -- this is bad
  data FreeM (X : Set) : Set where
    return : X -> FreeM X
    layer : act F (FreeM X) -> FreeM X

  {-# TERMINATING #-} -- a lie...
  FMF : Functor SET SET
  act FMF = FreeM
  fmap FMF f (return x) = return (f x)
  fmap FMF f (layer x) = layer (fmap F (fmap FMF f) x)
  identity FMF = ext lemma where
    lemma : ∀ x → fmap FMF (λ x → x) x ≡ x
    lemma (return x) = refl
    lemma (layer x) = cong layer (trans
                                   (cong (λ z → fmap F z x) (ext lemma))
                                   (cong-app (identity F) x))
  homomorphism FMF {X = X} {f = f} {g} = ext lemma where
    lemma : (x : FreeM X) → fmap FMF (λ x₁ → g (f x₁)) x ≡ fmap FMF g (fmap FMF f x)
    lemma (return x) = refl
    lemma (layer x) = cong layer (trans
                                   (cong (λ z → fmap F z x) (ext lemma))
                                   (cong-app (homomorphism F) x))

  {-# TERMINATING #-} -- a lie...
  join : ∀ {X} → FreeM (FreeM X) -> FreeM X
  join (return x) = x
  join (layer x) = layer (fmap F join x)
-}

{-# NO_POSITIVITY_CHECK #-} -- this is really bad
data Bad : Set where
  oops : (Bad -> ⊥) -> Bad

app : Bad -> Bad -> ⊥
app (oops f) y = f y

omega : Bad
omega = oops λ b → app b b

segfault : ⊥
segfault = app omega omega


-- So: free monads do not exist in general; we need to restrict to a
-- class of functors for which they do...

---------------------------------------------------------------------------
-- Now you try
---------------------------------------------------------------------------

record PointedSet : Set1 where
  constructor _,_
  field
    Carrier : Set
    point : Carrier
open PointedSet

record StrictMap (A B : PointedSet) : Set where
  constructor _,_
  field
    fun : Carrier A -> Carrier B
    preserves-* : fun (point A) ≡ point B
open StrictMap

eqStrictMap : {A B : PointedSet} -> {f g : StrictMap A B} ->
              fun f ≡ fun g -> f ≡ g
eqStrictMap {f = f} refl = cong (fun f ,_) (uip _ _)

POINTEDSET : Category
Obj POINTEDSET = PointedSet
Hom POINTEDSET = StrictMap
fun (id POINTEDSET) = λ x → x
preserves-* (id POINTEDSET) = refl
fun (comp POINTEDSET (f , p) (g , q)) = comp SET f g
preserves-* (comp POINTEDSET (f , p) (g , q)) = trans (cong g p) q
assoc POINTEDSET = eqStrictMap refl
identityˡ POINTEDSET = eqStrictMap refl
identityʳ POINTEDSET = eqStrictMap refl

forgetPoint : Functor POINTEDSET SET
forgetPoint = {!!}

open import Data.Maybe as Maybe using (Maybe; nothing; just; map)
open import Data.Maybe.Properties renaming (map-id to mmap-id; map-compose to mmap-compose)

addPoint : Functor SET POINTEDSET
addPoint = {!!}

addPoint⊣forgetPoint : Adjunction addPoint forgetPoint
addPoint⊣forgetPoint = {!!}

-- what is the monad induced by this adjunction?

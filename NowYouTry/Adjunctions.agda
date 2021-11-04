{-# OPTIONS --type-in-type #-}
module NowYouTry.Adjunctions where

open import Axiom.UniquenessOfIdentityProofs.WithK
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≤_)
open import Function using (_∘′_)

open import Lectures.Categories
open import Lectures.Kleisli
open import Lectures.Monads

open import Common.Category hiding (Monad)
open import Common.Category.Solver

---------------------------------------------------------------------------
-- Adjunctions
---------------------------------------------------------------------------

record Adjunction {C D : Category}
                  (F : Functor C D)
                  (G : Functor D C) : Set where

-- Notation: F ⊣ G, "F is left adjoint to G" or eq. "G is right adjoint to F"

  open Category
  open Functor
  open NaturalTransformation

  field
    to   : {X : Obj C}{B : Obj D} -> Hom D (act F X)        B  -> Hom C X         (act G B)         -- IMPORTANT
    from : {X : Obj C}{B : Obj D} -> Hom C X         (act G B) -> Hom D (act F X)        B          -- IMPORTANT
    left-inverse-of : ∀ {X B} →  (h : Hom D (act F X) B) -> from (to h) ≡ h                         -- (IMPORTANT)
    right-inverse-of : ∀ {X B} → (k : Hom C X (act G B)) -> to (from k) ≡ k                         -- (IMPORTANT)

--    for all X : Obj C, B : Obj D.
--
--            F X  -->   B      |         ^
--            ============      | to      | from
--              X  --> G B      v         |

    to-natural : {X X' : Obj C}{B B' : Obj D} (f : Hom C X' X)(g : Hom D B B') ->                   -- not so important
                   comp SET (to {X} {B}) (λ h → comp C f (comp C h (fmap G g)))
                     ≡
                   comp SET (λ k → comp D (fmap F f) (comp D k g)) (to {X'} {B'})


{-       for all f : X' -> X, g : B -> B'.

                            to {X} {B}
            Hom (F X) B   --------------> Hom X (G B)
                 |                            |
                 |                            |
    g ∘ _ ∘ F f  |                            | G g ∘ _ ∘ f
                 |                            |
                 |                            |
                 v                            v
                            to {X'} {B'}
            Hom (F X') B' --------------> Hom X' (G B')
-}

  from-natural : {X X' : Obj C}{B B' : Obj D} (f : Hom C X' X)(g : Hom D B B') ->
                 comp SET (from {X} {B}) (λ k → comp D (fmap F f) (comp D k g))
                   ≡
                 comp SET (λ h → comp C f (comp C h (fmap G g))) (from {X'} {B'})
  from-natural f g = SET ⊧begin
    < (λ k → comp D (fmap F f) (comp D k g)) > ∘Syn < from >
      ≡⟦ solveCat refl ⟧
    -[ idSyn ]- ∘Syn < (λ k → comp D (fmap F f) (comp D k g)) > ∘Syn < from >
      ≡⟦ reduced (rq (sym (ext left-inverse-of)) , rd , rd) ⟧
    -[ < from > ∘Syn < to > ]- ∘Syn < (λ k → comp D (fmap F f) (comp D k g)) >  ∘Syn < from >
      ≡⟦ solveCat refl ⟧
    < from > ∘Syn -[ < to > ∘Syn < (λ k → comp D (fmap F f) (comp D k g)) > ]- ∘Syn < from >
      ≡⟦ reduced (rd , rq (sym (to-natural f g)) , rd) ⟧
    < from > ∘Syn -[ < (λ h → comp C f (comp C h (fmap G g))) > ∘Syn < to > ]- ∘Syn < from >
      ≡⟦ solveCat refl ⟧
    < from > ∘Syn < (λ h → comp C f (comp C h (fmap G g))) > ∘Syn -[ < to > ∘Syn < from > ]-
      ≡⟦ reduced (rd , rd , rq (ext right-inverse-of))  ⟧
    < from > ∘Syn < (λ h → comp C f (comp C h (fmap G g))) > ∘Syn -[ idSyn ]-
      ≡⟦ solveCat refl ⟧
    < from > ∘Syn < (λ h → comp C f (comp C h (fmap G g))) >
      ⟦∎⟧

---------------------------------------------------------------------------
-- Adjoints to the forgetful functor PREORDER -> SET
---------------------------------------------------------------------------

open Category
open Functor
open Adjunction

open Preorder
open MonotoneMap

forget : Functor PREORDER SET
act forget X = Carrier X
fmap forget f = fun f
identity forget = refl
homomorphism forget = refl

-- A right adjoint to forget

chaoticPreorder : Functor SET PREORDER
Carrier (act chaoticPreorder B) = B
_≤_ (act chaoticPreorder B) b b' = ⊤
reflexive (act chaoticPreorder B) = tt
transitive (act chaoticPreorder B) _ _ = tt
propositional (act chaoticPreorder B) p q = refl
fun (fmap chaoticPreorder f) = f
monotone (fmap chaoticPreorder f) x y p = tt
identity chaoticPreorder = eqMonotoneMap refl
homomorphism chaoticPreorder = eqMonotoneMap refl

forget⊣chaotic : Adjunction forget chaoticPreorder
fun (to forget⊣chaotic h) = h
monotone (to forget⊣chaotic h) x y p = tt
from forget⊣chaotic k = fun k
left-inverse-of forget⊣chaotic h = refl
right-inverse-of forget⊣chaotic k = eqMonotoneMap refl
to-natural forget⊣chaotic f g = ext (λ x → eqMonotoneMap refl)

discretePreorder : Functor SET PREORDER
Carrier (act discretePreorder A) = A
_≤_ (act discretePreorder A) = _≡_
reflexive (act discretePreorder A) = refl
transitive (act discretePreorder A) = trans
propositional (act discretePreorder A) = uip
fun (fmap discretePreorder f) = f
monotone (fmap discretePreorder f) x y = cong f
identity discretePreorder = eqMonotoneMap refl
homomorphism discretePreorder = eqMonotoneMap refl

discrete⊣forget : Adjunction discretePreorder forget
to discrete⊣forget h = fun h
fun (from discrete⊣forget k) = k
monotone (from discrete⊣forget {B = B} k) x .x refl = reflexive B
left-inverse-of discrete⊣forget h = eqMonotoneMap refl
right-inverse-of discrete⊣forget k = refl
to-natural discrete⊣forget f g = refl









---------------------------------------------------------------------------
-- Binary coproducts as a left adjoint
---------------------------------------------------------------------------

PAIR : Category -> Category -> Category
Obj (PAIR C D) = Obj C × Obj D
Hom (PAIR C D) (A , X) (A' , X') = Hom C A A' × Hom D X X'
id (PAIR C D) = (id C , id D)
comp (PAIR C D) (f , g) (f' , g') = (comp C f f' , comp D g g')
assoc (PAIR C D) = cong₂ _,_ (assoc C) (assoc D)
identityˡ (PAIR C D) = cong₂ _,_ (identityˡ C) (identityˡ D)
identityʳ (PAIR C D) = cong₂ _,_ (identityʳ C) (identityʳ D)


diag : {C : Category} -> Functor C (PAIR C C)
act diag X = (X , X)
fmap diag f = (f , f)
identity diag = refl
homomorphism diag = refl

Either : Functor (PAIR SET SET) SET
act Either (A , B) = A ⊎ B
fmap Either (f , g) (inj₁ x) = inj₁ (f x)
fmap Either (f , g) (inj₂ y) = inj₂ (g y)
identity Either = ext (λ { (inj₁ x) → refl ; (inj₂ y) → refl})
homomorphism Either = ext (λ { (inj₁ x) → refl ; (inj₂ y) → refl })

Either⊣diag : Adjunction Either (diag {SET})
to Either⊣diag {X = (A , B)} {B = C} h = h ∘′ inj₁ , h ∘′ inj₂
from Either⊣diag {X = A , B} {B = C} (f , g) (inj₁ x) = f x
from Either⊣diag {X = A , B} {B = C} (f , g) (inj₂ y) = g y
left-inverse-of Either⊣diag h = ext (λ { (inj₁ x) → refl ; (inj₂ y) → refl })
right-inverse-of Either⊣diag (f , g) = refl
to-natural Either⊣diag f g = refl


---------------------------------------------------------------------------
-- Special cases of naturality (not very insightful)
---------------------------------------------------------------------------

to-natural₁ : {C D : Category}{F : Functor C D}{G : Functor D C} -> (adj : Adjunction F G) ->
              {X X' : Obj C}(f : Hom C X' X) ->
             comp C f (to adj (id D)) ≡ to adj (fmap F f)
to-natural₁ {C} {D} {F} {G} adj f = C ⊧begin
  < to adj (id D) > ∘Syn < f >
    ≡⟦ solveCat refl ⟧
  -[ (fmapSyn G idSyn ∘Syn < to adj (id D) >) ∘Syn < f > ]-
    ≡⟦ reduced (rq (cong-app (to-natural adj f (id D)) (id D))) ⟧
  < to adj (comp D (fmap F f) (comp D (id D) (id D))) >
    ≡⟦ reduced (rq (cong (to adj) (eqArr (solveCat {d = compSyn (fmapSyn F < f >) (compSyn idSyn idSyn)} {d' = fmapSyn F < f >} refl)))) ⟧
  < to adj (fmap F f) >
    ⟦∎⟧

to-natural₂ : {C D : Category}{F : Functor C D}{G : Functor D C} -> (adj : Adjunction F G) ->
                 {X : Obj C}{B' : Obj D}(g : Hom D (act F X) B') ->
                   comp C (to adj (id D)) (fmap G g) ≡ to adj g
to-natural₂ {C} {D} {F} {G} adj g = C ⊧begin
  fmapSyn G < g > ∘Syn < to adj (id D) >
    ≡⟦ solveCat refl ⟧
  (fmapSyn G < g > ∘Syn < to adj (id D) >) ∘Syn idSyn
    ≡⟦ reduced (rq (cong-app (to-natural adj (id C) g) (id D))) ⟧
  < to adj (comp D (fmap F (id C)) (comp D (id D) g)) >
    ≡⟦ reduced (rq (cong (to adj) ((eqArr (solveCat {d = compSyn (fmapSyn F idSyn) (compSyn idSyn < g >)} {d' = < g >} refl))))) ⟧
  < to adj g >
    ⟦∎⟧

from-natural₁ : {C D : Category}{F : Functor C D}{G : Functor D C} -> (adj : Adjunction F G) ->
                {X : Obj C}{B' : Obj D}(f : Hom C X (act G B')) ->
                 comp D (fmap F f) (from adj (id C)) ≡ from adj f
from-natural₁ {C} {D} {F} {G} adj f = D ⊧begin
   < from adj (id C) > ∘Syn fmapSyn F < f >
     ≡⟦ solveCat refl ⟧
  -[ (idSyn ∘Syn  < from adj (id C) >) ∘Syn fmapSyn F < f > ]-
     ≡⟦ reduced (rq (cong-app (from-natural {C} {D} {F} {G} adj f (id D)) (id C))) ⟧
   < from adj (comp C f (comp C (id C) (fmap G (id D)))) >
     ≡⟦ reduced (rq (cong (from adj) (eqArr (solveCat {d = compSyn < f > (compSyn idSyn (fmapSyn G idSyn))} {< f >} refl) ))) ⟧
   < from adj f >
     ⟦∎⟧

from-natural₂ : {C D : Category}{F : Functor C D}{G : Functor D C} -> (adj : Adjunction F G) ->
                {B B' : Obj D}(g : Hom D B B') ->
                 comp D (from adj (id C)) g ≡ from adj (fmap G g)
from-natural₂ {C} {D} {F} {G} adj g = D ⊧begin
  < g > ∘Syn < from adj (id C) >
    ≡⟦ solveCat refl ⟧
  -[ (< g > ∘Syn < from adj (id C) >) ∘Syn fmapSyn F idSyn ]-
    ≡⟦ reduced (rq (cong-app (from-natural adj (id C) g) (id C))) ⟧
  < from adj (comp C (id C) (comp C (id C) (fmap G g))) >
    ≡⟦ reduced (rq (cong (from adj) (eqArr (solveCat {d = compSyn idSyn (compSyn idSyn (fmapSyn G < g >))} {fmapSyn G < g >} refl)))) ⟧
  < from adj (fmap G g) >
    ⟦∎⟧

---------------------------------------------------------------------------
-- Monads from adjunctions
---------------------------------------------------------------------------

open Monad
open NaturalTransformation


monadFromAdj : (C D : Category)(F : Functor C D)(G : Functor D C) ->
               Adjunction F G -> Monad C
functor (monadFromAdj C D F G adj) = compFunctor F G
transform (returnNT (monadFromAdj C D F G adj)) X = to adj (id D)
natural (returnNT (monadFromAdj C D F G adj)) X Y f = trans (to-natural₁ adj f) (sym (to-natural₂ adj (fmap F f)))
transform (joinNT (monadFromAdj C D F G adj)) X = fmap G (from adj (id C))
natural (joinNT (monadFromAdj C D F G adj)) X Y f = C ⊧begin
 fmapSyn G < from adj (id C) >  ∘Syn fmapSyn G (fmapSyn F (fmapSyn G (fmapSyn F < f > )))
   ≡⟦ solveCat refl ⟧
 fmapSyn G (< from adj (id C) > ∘Syn fmapSyn F (fmapSyn G (fmapSyn F < f > )))
   ≡⟦ reduced (rq (cong (fmap G) (trans (from-natural₁ adj (fmap G (fmap F f))) (sym (from-natural₂ adj (fmap F f)))))) ⟧
 fmapSyn G (fmapSyn F < f > ∘Syn < from adj (id C) >)
   ≡⟦ solveCat refl ⟧
 fmapSyn G (fmapSyn F < f >) ∘Syn fmapSyn G < from adj (id C) >
   ⟦∎⟧
returnJoin (monadFromAdj C D F G adj) = C ⊧begin
  -[ fmapSyn G < from adj (id C) > ∘Syn < to adj (id D) > ]-
    ≡⟦ reduced (rq (to-natural₂ adj (from adj (id C)))) ⟧
  < to adj (from adj (id C)) >
    ≡⟦ reduced (rq (right-inverse-of adj (id C))) ⟧
  idSyn
    ⟦∎⟧
mapReturnJoin (monadFromAdj C D F G adj) = C ⊧begin
  fmapSyn G < from adj (id C) > ∘Syn fmapSyn G (fmapSyn F < to adj (id D) >)
    ≡⟦ solveCat refl ⟧
  fmapSyn G (< from adj (id C) > ∘Syn fmapSyn F < to adj (id D) >)
    ≡⟦ reduced (rq (cong (fmap G) (trans (from-natural₁ adj (to adj (id D))) (left-inverse-of adj (id D))))) ⟧
  fmapSyn G idSyn
    ≡⟦ solveCat refl ⟧
  idSyn
    ⟦∎⟧
joinJoin (monadFromAdj C D F G adj) = C ⊧begin
  fmapSyn G < from adj (id C) > ∘Syn fmapSyn G < from adj (id C) >
    ≡⟦ solveCat refl ⟧
  fmapSyn G (< from adj (id C) > ∘Syn < from adj (id C) >)
    ≡⟦ reduced (rq (cong (fmap G) (D ⊧begin
         -[ < from adj (id C) > ∘Syn < from adj (id C) > ]-
           ≡⟦ reduced (rq (from-natural₂ adj (from adj (id C)))) ⟧
         < from adj (fmap G (from adj (id C))) >
            ≡⟦ reduced (rq (sym (from-natural₁ adj (fmap G (from adj (id C)))))) ⟧
         < from adj (id C) > ∘Syn fmapSyn F (fmapSyn G < from adj (id C) >)
           ⟦∎⟧))) ⟧
  fmapSyn G (< from adj (id C) > ∘Syn fmapSyn F (fmapSyn G < from adj (id C) >))
      ≡⟦ solveCat refl ⟧
  fmapSyn G < from adj (id C) > ∘Syn fmapSyn G (fmapSyn F (fmapSyn G < from adj (id C) >))
    ⟦∎⟧

---------------------------------------------------------------------------
-- Every monad arises from an adjunction
---------------------------------------------------------------------------

ForgetKleisli : {C : Category}(M : Monad C) -> Functor (Kleisli M) C
act (ForgetKleisli M) X = Monad.act M X
fmap (ForgetKleisli M) f = bind M f
identity (ForgetKleisli M) = bindReturn M
homomorphism (ForgetKleisli {C} M) {Z = Z} {f = f} {g} =
  trans (cong (λ z → comp C (fmap (functor M) z) (join M Z)) (sym (assoc C))) (bindBind M {f = f} {g})

kleisliAdjunction : {C : Category}(M : Monad C) -> Adjunction (EmbedKleisli M) (ForgetKleisli M)
to (kleisliAdjunction M) f = f
from (kleisliAdjunction M) f = f
left-inverse-of (kleisliAdjunction M) h = refl
right-inverse-of (kleisliAdjunction M) h = refl
to-natural (kleisliAdjunction {C} M) f g = ext λ h →  C ⊧begin
  ((< join M _ > ∘Syn fmapSyn (functor M) < g >) ∘Syn < h >) ∘Syn < f >
    ≡⟦ solveCat refl ⟧
  -[ idSyn ]- ∘Syn < join M _ > ∘Syn fmapSyn (functor M) < g > ∘Syn < h > ∘Syn < f >
    ≡⟦ reduced (rq (sym (returnJoin M)) , rd , rd , rd , rd) ⟧
  -[ < join M _ > ∘Syn < return M _ > ]- ∘Syn < join M _ > ∘Syn fmapSyn (functor M) < g > ∘Syn < h > ∘Syn < f >
    ≡⟦ solveCat refl ⟧
  < join M _ > ∘Syn -[ < return M _ > ∘Syn < join M _ > ]- ∘Syn fmapSyn (functor M) < g > ∘Syn < h > ∘Syn < f >
    ≡⟦ reduced (rd , rq (natural (returnNT M) _ _ _) , rd , rd , rd) ⟧
  < join M _ > ∘Syn -[ fmapSyn (functor M) < join M _ > ∘Syn < return M _ > ]- ∘Syn fmapSyn (functor M) < g > ∘Syn < h > ∘Syn < f >
    ≡⟦ solveCat refl ⟧
  < join M _ > ∘Syn fmapSyn (functor M) < join M _ > ∘Syn -[ < return M _ > ∘Syn fmapSyn (functor M) < g > ]- ∘Syn < h > ∘Syn < f >
    ≡⟦ reduced (rd , rd , rq (natural (returnNT M) _ _ _) , rd , rd) ⟧
  < join M _ > ∘Syn fmapSyn (functor M) < join M _ > ∘Syn -[ fmapSyn (functor M) (fmapSyn (functor M) < g >) ∘Syn < return M _ > ]- ∘Syn < h > ∘Syn < f >
    ≡⟦ solveCat refl ⟧
  < join M _ > ∘Syn fmapSyn (functor M) < join M _ > ∘Syn fmapSyn (functor M) (fmapSyn (functor M) < g >) ∘Syn -[ < return M _ > ∘Syn < h > ]- ∘Syn < f >
    ≡⟦ reduced (rd , rd , rd , rq (natural (returnNT M) _ _ _) , rd) ⟧
  < join M _ > ∘Syn fmapSyn (functor M) < join M _ > ∘Syn fmapSyn (functor M) (fmapSyn (functor M) < g >) ∘Syn -[ fmapSyn (functor M) < h > ∘Syn < return M _ > ]- ∘Syn < f >
    ≡⟦ solveCat refl ⟧
  < join M _ > ∘Syn fmapSyn (functor M) (< join M _ > ∘Syn fmapSyn (functor M) < g > ∘Syn < h > ) ∘Syn < return M _ > ∘Syn < f >
    ⟦∎⟧

-- Theorem: monadFromAdj (kleisliAdjunction M) ≅ M

---------------------------------------------------------------------------
-- Now you try: binary products as a right adjoint
---------------------------------------------------------------------------

Both : Functor (PAIR SET SET) SET
act Both (A , B) = A × B
fmap Both = {!!}
identity Both = {!!}
homomorphism Both = {!!}

⊢diag : Adjunction (diag {SET}) Both
⊢diag = {!!}

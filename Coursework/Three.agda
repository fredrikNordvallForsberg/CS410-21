{-# OPTIONS --type-in-type --guardedness #-}
------------------------------------------------------------------------
-- CS410 Advanced Functional Programming 2021
--
-- Coursework 3
------------------------------------------------------------------------

module Coursework.Three where

----------------------------------------------------------------------------
-- COURSEWORK 3 -- TERMINAL OBJECTS AND TERMINAL APPLICATIONS
--
-- VALUE:     40% (divided over 80 marks, ie each mark is worth 0.5%)
-- DEADLINE:  5pm, Monday 6 December (Week 12)
--
-- SUBMISSION: Push your solutions to your own repo. Your last commit
-- before the deadline is your submitted version. However do get in
-- touch if you want to negotiate about extensions.
----------------------------------------------------------------------------

-- HINT: your tasks are labelled with the very searchable tag '???'

-- TIP: I have split up this file into a bunch of commented out
-- sections. When you reach a new section, you can search for it's
-- corresponding end tag (C-s in emacs) to comment it in and start
-- working on it.

open import Category.Applicative  using (RawApplicative)
open import Data.Char             using (Char)
open import Data.String as String using (String; fromList)
open import Data.Nat              using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties   -- you can use it all!
open import Data.Bool             using (Bool; true; false; if_then_else_)
open import Data.List   as L      using (List; []; _∷_; map)
open import Data.List.Properties  using (map-id; map-compose)
open import Data.Vec   as V
  using (Vec; []; _∷_; _++_; replicate; map; splitAt)
open import Data.Product          using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; map)
open import Data.Sum   as Sum     using (_⊎_; inj₁; inj₂; map)
open import Data.Unit             using (⊤; tt)
open import Data.Empty            using (⊥; ⊥-elim)
open import Function   as F       using (_∘′_; id)
open import IO.Primitive          using (IO)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; cong-app; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary      using (¬_; Dec; yes; no)

open import Common.Category
open import Common.Category.Solver
open import Lectures.Categories

open import Common.Display


------------------------------------------------------------------------------
--  A Baby but Important Universal Property (10 MARKS in total)
------------------------------------------------------------------------------

module _ (C : Category) where
  open Category

-- Often concepts in category theory can be phrased as so-called
-- universal properties: we can describe an object as the "best"
-- object with a certain property, in the sense that all other objects
-- with the same property maps into the given object. A simple example
-- is the notion of a *terminal* object: this is an object such that
-- every other object has a /unique/ morphism into it. We can describe
-- this as follows:

  record IsTerminal (X : Obj C) : Set where
    field
      mediate : {Y : Obj C} → Hom C Y X
      unique : {Y : Obj C} → (h : Hom C Y X) → h ≡ mediate {Y}

-- Some categories have terminal objects, others don't. Let us
-- consider some examples.

{- ??? 3.1 Show that SET has a terminal object.
   (1 MARK) -}

module _ where
  open IsTerminal

  SET-has-terminal-object : IsTerminal SET {!!}
  SET-has-terminal-object = {!!}

{- ??? 3.2 Show that MONOID has a terminal object.
  (2 MARKS) -}

-- HINT: Remember that you can use eqMonoidMorphism to prove that two
-- monoid morphisms are equal.

module _ where
  open IsTerminal

  MONOID-has-terminal-object : IsTerminal MONOID {!!}
  MONOID-has-terminal-object = {!!}

{- ??? 3.3 Show that not every category has a terminal object.
   (3 MARKS) -}

module _ where
  open Category
  open IsTerminal

  C : Category
  C = {!!}

  no-terminal : (X : Obj C) → ¬ IsTerminal C X
  no-terminal = {!!}

module _ (C : Category) where
  open Category
  open IsTerminal

  -- This is what it means for two objects in a category to be
  -- isomorphic (note how isomorphisms of sets from Coursework.Two is
  -- a special case, in the category SET):

  record _≅_ (X Y : Obj C) : Set where
    field
      to : Hom C X Y
      from : Hom C Y X
      left-inverse-of : comp C from to ≡ Category.id C
      right-inverse-of : comp C to from ≡ Category.id C
  open _≅_

{- ??? 3.4 Show that terminal objects are unique up to isomorphism: If
       X and Y are both terminal, then X ≅ Y.
   (4 MARKS) -}

  terminal-objects-unique : (X Y : Obj C) → IsTerminal C X → IsTerminal C Y → X ≅ Y
  terminal-objects-unique = {!!}


{- annan UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------------------------------------------------
--  All and Any (20 MARKS in total)
------------------------------------------------------------------------------

-- Before we get started building more exciting things, let us equip
-- ourselves with some mathematical kit. The All data type records
-- that a given property holds for all elements of a list:

data All {A : Set} (P : A -> Set) : List A -> Set where
  []  : All P []
  _∷_ : ∀ {x xs} → (px : P x) -> (pxs : All P xs) -> All P (x ∷ xs)

-- And the Any data type records that a given property holds for some
-- element of a list:

data Any {A : Set} (P : A -> Set) : List A -> Set where
  here : ∀ {x xs} → (px : P x) -> Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs -> Any P (x ∷ xs)

{- ??? 3.5 To get a feel for All and Any, show that every element of
       list0 is odd, that there is an odd element in list1, and that
       there are no odd elements in list2.
   (3 MARKS) -}

data IsOdd : ℕ -> Set where
  one : IsOdd (suc zero)
  sucsuc : ∀ {n} → IsOdd n -> IsOdd (suc (suc n))

list0 list1 list2 : List ℕ
list0 = 1 ∷ 5 ∷ 9 ∷ []
list1 = 0 ∷ 0 ∷ 4 ∷ 201 ∷ 92 ∷ []
list2 = 2 ∷ 6 ∷ 4 ∷ 10 ∷ []

allOdd0 : All IsOdd list0
allOdd0 = {!!}

-- This could come in handy:
isOdd2*x+1 : (n : ℕ) -> IsOdd (suc (2 * n))
isOdd2*x+1 = {!!}

someOdd1 : Any IsOdd list1
someOdd1 = {!!}

notAllOdd2 : ¬ All IsOdd list2
notAllOdd2 = {!!}

notSomeOdd2 : ¬ Any IsOdd list2
notSomeOdd2 = {!!}

------------------------------
--  All and Any are functorial
------------------------------

{- ??? 3.6 Show that All is a functor from I-indexed sets to List
       I-indexed sets.
   (2 MARKS) -}

All-map : {I : Set}{P Q : I → Set} → (∀ i → P i →  Q i) → (∀ is → All P  is → All Q is)
All-map = {!!}

Any-map : {I : Set}{P Q : I → Set} → (∀ i → P i →  Q i) → (∀ is → Any P  is → Any Q is)
Any-map = {!!}

  {- ??? 3.7 Okay, now show that I-indexed sets form a category, and
         that All and Any *really are* functors from I-indexed sets to List
         I-indexed sets. (You can use function extensionality for the
         proofs.)
     (5 MARKS) -}

module _ where
  open Category
  open Functor

  _-C>_ : (I : Set) -> (C : Category) -> Category
  I -C> C = {!!}

  ALL : {I : Set} -> Functor (I -C> SET) (List I -C> SET)
  ALL = {!!}

  ANY : {I : Set} -> Functor (I -C> SET) (List I -C> SET)
  ANY = {!!}

{- ??? 3.8 How are "there is an element not satisfying P" and "not
       every element satisfies P" related? Show that We can always go
       from more information to less, and also the other way, if the
       predicate P is decidable.
   (4 MARKS) -}

Any¬→¬All : {I : Set} → {P : I → Set} → {xs : List I} →
              Any (¬_ ∘′ P) xs → ¬ All P xs
Any¬→¬All = {!!}

¬All→Any¬ : {I : Set} → {P : I → Set} → {xs : List I} →
            (∀ i → Dec (P i)) →
            ¬ All P xs → Any (¬_ ∘′ P) xs
¬All→Any¬ = {!!}

-- TO PONDER: What if P is not decidable? Can you show that ¬All→Any¬
-- in that case cannot be implementable?

module _ {X Y}(f : X -> Y){P : Y -> Set} where

-- What is the relationship between
--   All (λ x → P (f x)) xs
-- and
--   All P (L.map f xs) ?
-- Both types say that P (f x) holds for every x in xs, but the types
-- are not obviously the same, so a proof is required to that effect.

{- ??? 3.9 Show that you can translate back and forth between the two
       types.
   (1 MARK) -}

  allReindex : ∀ is → All (P ∘′ f) is → (All P ∘′ L.map f) is
  allReindex = {!!}

  allReindex⁻¹ : ∀ is → (All P ∘′ L.map f) is → All (P ∘′ f) is
  allReindex⁻¹ = {!!}

--------------------------
-- Applicative structure
--------------------------

-- Remember applicatives? Vectors are applicative in the following
-- way:

VApp : ∀ n -> RawApplicative (λ X -> Vec X n)
VApp n = record { pure = replicate ; _⊛_ = V._⊛_ }

-- As incidentally suggested by the name, we will have use of
-- applicative functors in the building of applications. Hence we need
-- to build up some applicative machinery for All:

  {- ??? 3.10 Show that you can yank applicative structure out through
         All.
     (2 MARKS)
  -}

module _ {F : Set -> Set}(ApF : RawApplicative F) where
  open RawApplicative ApF

  allYank : ∀ {X}{P : X -> Set} → ∀ is → All (F ∘′ P) is → (F ∘′ All P) is
  allYank = {!!}

{- ??? 3.11 Find the *indexed* applicative structure for All. (This
       sadly does not fit in the RawApplicative record of the standard
       library, as it is not formulated for arbitrary categories.)
   (1 MARK)
-}

-- HINT: this is very similar to what happens for vectors.

pureAll : ∀ {I}{P : I -> Set} → (∀ i → P i) -> (∀ is → All P is)
pureAll = {!!}

appAll  : ∀ {I}{P Q : I -> Set} → ∀ is → All (λ i → P i → Q i) is → All P is → All Q is
appAll = {!!}

{- ??? 3.12 Implement transposition:
   (2 MARKS)
-}

-- HINTS:
-- (i)  This is a classic exercise in deploying applicative structure.
-- (ii) This is not just for fun; you will need this later.

transpose : {I J : Set}{R : I -> J -> Set}
            {is : List I}{js : List J}
  -> All (λ i -> All (λ x → R i x) js) is  -- If every i is related to every j,
  -> All (λ j -> All (λ x → R x j) is) js  -- show every j is related to every i.
transpose = {!!}

END OF COMMENT annan -}

{- banff UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------------------------------------------------
-- CUTTING THINGS UP (20 MARKS in total)
------------------------------------------------------------------------------

-- In the rest of this Coursework, we will build a window manager in a
-- structured way. This means that we need to be able to cut up the
-- screen in different ways in order to display different windows, so
-- let us first develop the tools to talk about cuts in that way. The
-- following definition can be used to describe how an O can be cut up
-- into a finite list of I-pieces:

record _<|_ (O I : Set) : Set where
  constructor _<!_
  field
    Cuts    : O -> Set  -- for every o : O, there is a set of ways to cut it
    pieces  : {o : O} -> Cuts o -> List I
                        -- and for each cut, there is a list of pieces
open _<|_

-- This is our runnning and motivating example:


NatCut : ℕ <| ℕ
Cuts NatCut z = Σ ℕ \ x -> Σ ℕ \ y -> (x + y) ≡ z
pieces NatCut (x , y , _) = x ∷ y ∷ []

-- See? To cut a natural number z, you choose two numbers x and y such
-- that their sum is x, and the pieces of such a cut is x and y
-- themselves.

-- The following "meaning" of cuts explains how one makes a cut, and
-- decorates all the pieces with a given P : I → Set:

⟦_⟧ : {O I : Set} -> O <| I -> (I -> Set) -> (O -> Set)
⟦ Cu <! ps ⟧ P o = Σ (Cu o) \ c    -- choose a way to cut o
                    -> All P (ps c)  -- then decorate all the pieces with P


{- ??? 3.13 For intuition, cut up 12 into two odd pieces.
   (1 MARK)
-}

cut12 : ⟦ NatCut ⟧ IsOdd 12
cut12 = {!!}


{- ??? 3.14 Extend ⟦_⟧ to a functor.
  (2 MARKS) -}

  -- HINT: It's okay for you to use function extensionality here,
  -- because we won't need to run the proofs from this section in the
  -- final program. You might also find `cong-app`, the inverse of
  -- function extensionality, useful.

module _ {O I : Set} where

  open Functor

  ⟦_⟧F : (F : O <| I) -> Functor (I -C> SET) (O -C> SET)
  ⟦ x ⟧F = {!!}

------------------------------
-- Cutting and cutting again
------------------------------

module _ {I : Set}(F : I <| I)(X : I -> Set) where

  -- Think of X : I → Set as a predicate telling us which i : I we
  -- like. The operation ⟦_⟧ let's us make one cut. If I = O, then we
  -- can keep cutting, until we hopefully have pieces that we
  -- like. This is captured in the following definition:

  data ManyCuts (i : I) : Set where
    stop : X i -> ManyCuts i
    <_> : ⟦ F ⟧ ManyCuts i -> ManyCuts i

{- ??? 3.15 Making *at least two cuts*, cut up 8 into many odd pieces.
   (1 MARK) -}

cut8 : ManyCuts NatCut IsOdd 8
cut8 = {!!}

module _ {I : Set}(F : I <| I)
         {X Y : I -> Set}             -- Suppose we can turn...
         (s : ∀ i → X i → Y i)            -- ... stop conditions into Ys, and ...
         (c : ∀ i → ⟦ F ⟧ Y i → Y i)      -- ... cuts made of Ys into Ys...
       where


  {- ??? 3.16 ... show that we can then turn ManyCuts X into Ys.
    (1 MARK) -}

  -- HINT: You will need to mutually define functoriality of All again
  -- to get the termination checker to play along.

  manyCutsIter : ∀ i → ManyCuts F X i → Y i
  manyCutsIter = {!!}

-- An important special case of manyCutsIter is a bind operation for ManyCuts:

manyCutsBind : {I : Set}(F : I <| I){X Y : I -> Set} ->
               (∀ i → X i → ManyCuts F Y i) -> ∀ i → ManyCuts F X i → ManyCuts F Y i
manyCutsBind F k = manyCutsIter F k (λ i → <_>)

{- ??? 3.17 Use manyCutsBind to implement "map" and "join" for ManyCuts.
       They are both one-liners.
   (1 MARK) -}

ManyCuts-map : {I : Set}(F : I <| I){X Y : I -> Set} ->
               (∀ i → X i → Y i) -> ∀ is → ManyCuts F X is → ManyCuts F Y is
ManyCuts-map = {!!}

manyCutsJoin : {I : Set}(F : I <| I){X : I -> Set} ->
               ∀ i → ManyCuts F (ManyCuts F X) i → ManyCuts F X i
manyCutsJoin = {!!}


{- ??? 3.18 Show that replacing stop by stop and cuts by cuts does nothing.
  (2 MARKS) -}

-- HINT: You might want to do something simultaneous.

manyCutsIterId : {I : Set}{F : I <| I}{X : I -> Set} →
                 (i : I) → manyCutsIter F (λ i → stop {X = X}) (λ i → <_>) i ≡ id
manyCutsIterId = {!!}

module _ {I : Set}{F : I <| I} where

  -- The following result can be deployed in many different situations.

  module _ {W X Y : I -> Set}
           (k : ∀ i → W i → ManyCuts F X i)   -- how to grow more ManyCuts
           (s : ∀ i → X i → Y i)          -- how to eat stop
           (c : ∀ i → ⟦ F ⟧ Y i → Y i)  -- how to eat cuts
           where
    open Category (I -C> SET) hiding (_⇒_)


    {- ??? 3.19 Show that growing a ManyCuts with manyCutsBind then eating the result
           gives the same result as eating the original with more eating at the leaves.
      (2 MARKS) -}

    -- HINT: This is similar to manyCutsIterId.

    manyCutsBindIter : comp (manyCutsBind F k) (manyCutsIter F s c)
                     ≡
                   manyCutsIter F (comp k (manyCutsIter F s c)) c
    manyCutsBindIter = {!!}

  -- Suitably tooled up, go for the win.

  module _  where
    open Category (I -C> SET)
    open Functor
    open NaturalTransformation
    open Monad

    {- ??? 3.20 You have implemented "map" and "join".  Prove that you
           have a functor and a monad.
      (4 MARKS) -}

    -- HINT: manyCutsBindIter instantiated many different ways is your
    -- friend here for the proofs.

    MANYCUTS : Functor (I -C> SET) (I -C> SET)
    MANYCUTS = {!!}

    manyCutsMonad : Monad (I -C> SET)
    manyCutsMonad = {!!}

END OF COMMENT banff -}

{- cumbernauld UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------
--  Cutting in Multiple Dimensions
------------------------------------

-- If we know how to cut up numbers (seen as lengths), we ought to be able
-- to cut up pairs of numbers (see as the width and height of a rectangle).

-- Let's approach the problem in small steps.


{- ??? 3.21 Angelic choice of cutting. (Here "angelic" means *you* get
       to choose which sort of cut to make.)
   (2 MARKS)
-}

-- Specification:
-- (i)   We get two different schemes for cutting the same sort of Os into Is.
-- (ii)  Combine them by offering to cut in accordance with either scheme.
-- (iii) The pieces should then be those given for the chosen cut in the
--       chosen scheme.

_>+<_ : forall {O I} -> O <| I -> O <| I -> O <| I
(x >+< y) = {!!}

{- ??? 3.22 Right and Left Framing.
   (2 MARKS)
-}

-- Specification:
-- These operators should generate higher dimensional cutting schemes
-- from some lower dimensional C,
-- by attaching an extra dimension, J,
-- which is never affected by a cut.
-- That is, the given value in O should determine the choice of cuts
-- according to C. All pieces should inherit the given value in J.


_>|_ : forall {O I}      (C : O <| I) J   ->      (O × J) <|     (I × J)
(x >| J) = {!!}

_|<_ : forall {O I}    J (C : O <| I)     ->  (J × O)     <| (J × I)
(J |< x) = {!!}

-- Intuition:
-- If you know how to cut up a number into parts, then you know how to
-- cut up a rectangle whose width is that number into subrectangles
-- whose widths are the parts. The height of the original rectangle
-- is then the height of all of its parts.


{- ??? 3.23 Combining Separate Dimensions
   (1 MARK)
-}

-- Specification:
-- (i)   We have two separate dimensions, indexed by I and J, respectively.
-- (ii)  We know, separately, a scheme for cutting each dimension.
-- (iii) We want a cutting scheme which allows us
--         either to cut the I dimension, preserving the J index,
--         or     to cut the J dimension, preserving the I index.

-- HINT: use framing and angelic choice, of course!

_|+|_ : forall {I J} -> I <| I -> J <| J -> (I × J) <| (I × J)
F |+| G = {!!}


-- Having taken those small steps, we now have a scheme for cutting up
-- rectangles with axis-aligned cuts, either somewhere along their
-- width or somewhere along their height.

RectCut : (ℕ × ℕ) <| (ℕ × ℕ)
RectCut = NatCut |+| NatCut


{- ??? 3.24 To make sure we know what is going on, tile a rectangular
       area with square pieces.
   (1 MARK)
-}

data Square : ℕ × ℕ -> Set where
  square : (n : ℕ) -> Square (n , n)

-- NOTE: you can't make a Square (w , h) unless w and h are equal.

-- Specification:
-- (i)   If your current goal has equal width and height, stop.
-- (ii)  Otherwise, cut your rectangle into two pieces, the first of which
--       is square.

example : ManyCuts RectCut Square (10 , 6)
example = {!!}

-- TO PONDER: if you ignore the specification, is this the only way to square the rectangle?

END OF COMMENT cumbernauld -}

{- dollar UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------------------------------------------------
--  After Cut Comes Paste (20 MARKS in total)
------------------------------------------------------------------------------

-- As we have seen, a notion of "cutting" induces a functor.  The
-- corresponding algebras are "pasting" operators: they take a cut up
-- thing and puts it back together again.

Pasting : forall {I}(C : I <| I)(X : I -> Set) -> Set
Pasting C X = ∀ i → ⟦ C ⟧ X i → X i


{- ??? 3.25 Find the component that gives vectors a pasting operator
       for NatCut in Data.Vec.
  (1 MARK)
-}

vecPaste : forall {X} -> Pasting NatCut (Vec X)
vecPaste = {!!}

-- We can now use the kit you built earlier to combine pasting
-- algebras for multiple dimensions:

compPaste : ∀ {I J}                -- What we get:
  -> (C : I <| I)(F : Set -> I -> Set)  -- C cuts correspond to F layers

  -> (D : J <| J)(G : Set -> J -> Set)  -- D cuts correspond to G layers
  -> (∀ j → RawApplicative \ X -> G X j)  -- and G is always applicative

  -> (∀ {X} → Pasting C (F X))    -- polymorphic C-paster for F
  -> (∀ {X} → Pasting D (G X))    -- polymorphic D-paster for G
                                        -- What we want:
  -> (∀ {X} → Pasting (C |+| D) (λ { (i , j) -> G (F X i) j}))
     -- a polymorphic two-dimensional paster for Gs of Fs
compPaste C F D G ApG cf dg (i , j) (inj₁ c , ps)
  = pure (cf i) ⊛ (pure (c ,_) ⊛ allYank (ApG j) _ (allReindex⁻¹ _ _ ps))
  where open RawApplicative (ApG j)
compPaste C F D G ApG cf dg (i , j) (inj₂ d , ps)
  = dg j (d , allReindex⁻¹ _ _ ps)


{- ??? 3.26 Use compPaste to give a one-line RectCut-paster for Matrix
       (a vector of vectors, see Common.Display) dimensions.
   (1 MARK)
-}

matPaste : ∀ {X} → Pasting RectCut (Matrix X)
matPaste = {!!}


{- ??? 3.27 In one line, using previous components but no pattern
       matching, show how to paste together a Matrix from a ManyCuts whose
       leaves each map to a Matrix.
  (1 MARK)
-}

manyCutsMatrix : ∀ {X P} → (∀ i →  P i → Matrix X i) -> ∀ i → ManyCuts RectCut P i → Matrix X i
manyCutsMatrix = {!!}


END OF COMMENT dollar -}

{- elie UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

--------------------
-- The List Relator
--------------------

-- Let us take a break and collect some more down-to-Earth marks by
-- considering the *relational* action of lists, by lifting a binary
-- relation on elements pointwise to a binary relation on lists of
-- elements. This is like All, but for relations, not predicates.

data Pointwise {X Y : Set}(R : X -> Y -> Set) : List X -> List Y -> Set where
  []   : Pointwise R [] []
  _∷_ : ∀ {x xs y ys} → R x y -> Pointwise R xs ys -> Pointwise R (x ∷ xs) (y ∷ ys)

-- As you can see, two lists are related by Pointwise R if
--   (i)  their lengths are equal
--   (ii) the elements in corresponding positions are related by R.

-- We will shortly make use of Pointwise, so you need to build some equipment.

{- ??? 3.28 Show that every list is pairwise equal to itself.
   (1 MARK)
-}

Pointwise-refl : forall {X}(xs : List X) -> Pointwise _≡_ xs xs
Pointwise-refl = {!!}

{- ??? 3.29 Build fmap for Pointwise, suitably "over" L.map.
   (1 MARK)
-}

Pointwise-map : ∀ {A B C D}
        (f : A -> C)(g : B -> D)   -- functions source to target
        {R : A -> B -> Set}        -- relation on source types
        {S : C -> D -> Set}        -- relation on target types
     -> (∀ {a b} → R a b -> S (f a) (g b))  -- source implies target
     -- Now, show why the target lists are related if the source lists are.
     -> ∀ {as bs} → Pointwise R as bs -> Pointwise S (L.map f as) (L.map g bs)
Pointwise-map = {!!}

END OF COMMENT elie -}

{- fortrose UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

-----------------------------------------------------
-- Cutting Things Up And Sticking Them Back Together
-----------------------------------------------------

-- This section is the heart of the exercise. It deals with the
-- situation where you have a structure that is subdivided in one way,
-- but you need it to be subdivided in another. That's a situation
-- which arises when you need to display multiple layers of
-- overlapping windows. The cutting structure of the front layer
-- determines which parts of the back layers you can see. So you will
-- need to *impose* the front structure onto the back layer, in order
-- to extract its visible parts.

module _ {I}(C : I <| I) where  -- we fix some notion of cutting

  -- A "Cutter" is a way of taking a *whole* thing and *choosing* how to cut
  -- it into the specified collection of *pieces*.

  Cutter : (I -> Set) -> Set
  Cutter P = {i : I}(c : Cuts C i)   -- given a size, choose how to cut
          -> P i                     -- and, given a whole P,
          -> All P (pieces C c)      -- get all the P pieces for your cut


{- ??? 3.30 For this concept to sink in, construct a NatCut cutter for
       vectors.
  (1 MARK) -}

-- HINT: As usual, it is worth checking the import list for Data.Vec.

vecCutter : forall {X} -> Cutter NatCut (Vec X)
vecCutter = {!!}

module _ {I}(C : I <| I) where  -- we fix some notion of cutting

  -- Now, working in ManyCuts NatCut, consider that we might have a structure
  -- which has a top level cut in one place:
  --
  --        <---tl---||--------tr-------->
  --
  -- But suppose we *wish* that it was cut differently, e.g., here:
  --
  --        <--------wl--------||---wr--->
  --
  -- If we are able to cut up the recursive substructures wherever we want,
  -- we can make our wish come true.
  --
  -- Project the cut we want onto the cut we've got. And cut there!
  --
  --        <--------wl--------||---wr--->
  --                           ||
  --                           vv
  --        <---tl---||--------tr-------->
  --        <---tl---|<--trl---||--trr-->>
  --
  -- That is, we leave the left piece alone and cut the right piece in two.
  -- In general, some pieces will be left alone; others will be cut.
  --
  -- We now have three pieces from which we can assemble the structure we
  -- need. How to do that?
  --
  -- Project the cut we've got onto the cut we want. And cut there!
  --
  --        <---tl---||--------tr-------->
  --                 ||
  --                 vv
  --        <--------wl--------||---wr--->
  --        <<--wll--||---wlr-->|---wr--->
  --
  -- In general, some pieces we want will be whole. Others will need to
  -- be assembled from multiple sub-pieces.
  --
  -- We now have the sizes we need. To finish the job, we just need the
  -- means to rearrange the pieces we've got into the structure we want.
  --
  --        <---tl---|<--trl---||--trr-->>
  --        <<--wll--||---wlr-->|---wr--->

  -- The following type captures the idea of being kept whole or cut further.

  SubCut : List I    -- a list of sub-piece sizes
        -> I         -- the size of the whole piece
        -> Set
  SubCut is i
    = (is ≡ (i ∷ []))  -- kept whole: there is one sub-piece,
                         -- with the same size as the piece
    ⊎ (Σ (Cuts C i) \ d -> is ≡ pieces C d)  -- cut further
    -- ^^ there was a cut,  ^^ and the sub-pieces are that cut's pieces

  -- Now your turn. Hopefully this helps you get the idea.

  {- ??? 3.31 Assemble pieces from sub-pieces.
    (1 MARKS)
  -}

  glueSubCut : forall {P}
    -> {iss : List (List I)}       -- 2-layer list of sub-pieces you have
    -> {is : List I}               -- 1-layer list of pieces you want
    -> (ds : Pointwise SubCut iss is)  -- how sub-pieces relate to pieces
    -> All (All (ManyCuts C P)) iss    -- now, given manyCutss as sub-pieces,
    -> All (ManyCuts C P) is           -- make the pieces!
  glueSubCut = {!!}

  -- What's the general recipe? Here goes.

  Recutter : Set
  Recutter =
    -- You get this information:
       {i : I}                         -- the size of the whole
    -> (c : Cuts C i)                  -- the cut we want
    -> (c' : Cuts C i)                 -- the cut we've been given
    -- You produce this information:
    -> Σ (List (List I)) λ iss  →        -- 2-layer list of wanted sub-pieces
       Σ (List (List I)) \ iss' →        -- 2-layer list of given sub-pieces
       Pointwise SubCut iss (pieces C c) ×   -- wanted sub-pieces fit wanted cut
       Pointwise SubCut iss' (pieces C c') × -- given sub-pieces fit given cut
       (∀ {P}                -- whatever the pieces are,
        -> All (All P) iss'  -- take the given sub-pieces and
        -> All (All P) iss)   -- deliver the wanted sub-pieces

  -- Now, let's work with stuff in Q for which we have a cutter,
  -- and suppose we possess a Recutter.

  module _ {Q}(cutQ : Cutter C Q)(recut : Recutter) where

    {- ??? 3.32 Build a Cutter for ManyCuts.
      (1 MARKS)
    -}

   -- HINTS:
    -- (i) Mutual recursion will probably be necessary; I've given you
    -- a gadget to cut pieces into sub-pieces to be mutually recursive
    -- with.
    -- (ii)  Each ManyCuts is either a stop, or a node made by some cut you don't want,
    --       but you have the equipment to deal with either situation.
    -- (iv)  "manyCutsCutter" will also need "glueSubCut"

    manyCutsCutter : Cutter C (ManyCuts C Q)
    chopSubCut :
         {iss' : List (List I)}          -- sub-piece sizes
      -> {is' : List I}                  -- piece sizes
      -> (ds' : Pointwise SubCut iss' is')   -- how sub-pieces come from pieces
      -> All (ManyCuts C Q) is'              -- now, given the pieces
      -> All (All (ManyCuts C Q)) iss'       -- produce the sub-pieces

    manyCutsCutter = {!!}

    chopSubCut = {!!}

    -- And, with that, we're ready to build the key device for working with
    -- overlays.


    {- ??? 3.33 Show that if you can combine a front *piece* with back
           *many cuts*, then you can combine front *many cuts* with back *many cuts*.
      (1 MARK)
    -}

    -- HINT: manyCutsIter and appAll are your friends here.

    overlay : ∀
         {P}  -- the type of pieces in the front layer
      --  Q, from module parameter above gives the type of pieces at the back
         {R}  -- the type of pieces in the combined output
      -> (∀ i →            P i → ManyCuts C Q i → ManyCuts C R i)  -- front piece on back manyCuts
      -> (∀ i → ManyCuts C P i → ManyCuts C Q i → ManyCuts C R i)  -- front manyCuts on back manyCuts
    overlay f = {!!}


-------------------------
-- Cutters for Matrices
-------------------------

-- A cutter for matrices is a special case of the general idea that
-- if we know how to cut in each dimension separately, we ought to be able
-- to cut multidimensional things, provided we have enough structure to
-- apply "inner" cuts through "outer" layers.
--
-- E.g., as a matrix is a column of rows, cutting vertically is cutting the
-- column, but cutting horizontally is cutting *all* the rows in the column.


{- ??? 3.34 Combine two dimensions of cutting.
   (2 MARKS)
-}

compCut :
  -- What's the general setup?
  ∀ {I J} → -- we have an I dimension and a J dimension
     (C : I <| I)(F : Set -> I -> Set)
     -- "inner" dimension with C-cuts corresponds to layers of F
  -> (D : J <| J)(G : Set -> J -> Set)
     -- "outer" dimension with D-cuts corresponds to layers of G
  -- What do we know about G?
  -> (∀ {X Y j} → (X -> Y) -> G X j -> G Y j)
     -- it has a suitable "map" operator
  -> (∀ {P : I -> Set}{is}{j} → G (All P is) j -> All (\ i -> G (P i) j) is)
     -- you can "yank" All through it (i.e., it's "traversable")
  -- Now what's the deal? You get
  -> (∀ {X} → Cutter C (F X))  -- a polymorphic C-cutter for Fs
  -> (∀ {X} → Cutter D (G X))  -- a polymorphic D-cutter for Gs
  -- and you make a
  -> ∀ {X} → -- polymorphic
        Cutter (C |+| D) -- two-dimensional cutter
          λ { (i , j) -> G (F X i) j}  -- for Gs full of Fs.
compCut = {!!}

{- ??? 3.35 Show that you can "yank" through vectors, and thus acquire your
-- matrix cutter.
   (1 MARK)
-}

-- HINT: Time to bring out that All structure again!

vecYank : {P : ℕ -> Set} {is : List ℕ} {j : ℕ} ->
          Vec (All P is) j -> All (\ i -> Vec (P i) j) is
vecYank = {!!}

matrixCutter : ∀ {X} → Cutter RectCut (Matrix X)
matrixCutter = {!!}

-------------------------
-- A Recutter for NatCut
-------------------------

-- In order to implement a recutter for NatCat, you will need to
-- analyse the situation where you have the *same* number, n, cut up
-- in two *different* ways, namely as (x + x') and as (y + y').

-- There are three possibilities:

-- x might be less than y (making x' greater than y')
--    <--------------------n------------------>
--    <-----x-----><------------x'------------>
--    <----------y--------><---------y'------->

-- x might be equal to y (making x' equal to y')
--    <--------------------n------------------>
--    <-----------x-----><---------x'--------->
--    <-----------y-----><---------y'--------->

-- x might be greater than y (making x' less than y')
--    <--------------------n------------------>
--    <----------x--------><---------x'------->
--    <-----y-----><------------y'------------>

-- The following view presents all these possibilities:

data CutCompare (x x' y y' n : ℕ) : Set where
  cutLt : (d : ℕ) -> x + suc d ≡ y -> suc d + y' ≡ x' -> CutCompare x x' y y' n
  cutEq : x ≡ y -> x' ≡ y' -> CutCompare x x' y y' n
  cutGt : (d : ℕ) -> y + suc d ≡ x -> suc d + x' ≡ y' -> CutCompare x x' y y' n


{- ??? 3.36 Show that you can always compare two NatCuts in this sense.
   (2 MARKS)
-}

cutCompare : ∀ x x' y y' {n} -> x + x' ≡ n -> y + y' ≡ n -> CutCompare x x' y y' n
cutCompare = {!!}

{- ??? 3.37 Now use cutCompare to build yourself a natRecutter.
   (2 MARKS)
-}

natRecutter : Recutter NatCut
natRecutter = {!!}

-------------------------------------
-- Recutters in Multiple Dimensions
-------------------------------------

-- Now that you can recut lengths, it's time to show that you can
-- recut rectangles. In fact, if you can recut individual dimensions,
-- you can recut in any choice of dimensions.

module _                                -- You get:
    {I J}(C : I <| I)(D : J <| J)       -- notions of cut for two dimensions
    (rC : Recutter C)(rD : Recutter D)  -- recutters in both dimensions
  where

  {- ??? 3.38 Construct a recutter for the pair of dimensions, where each cut can
         be in either dimension.
     (4 MARKS)
  -}

-- Hints:
-- (i)   You will find you have four cases, two for each of the following
--       situations:
--       Either the cut wanted and the cut given are in the same dimension
--         (and you have a recutter for that dimension),
--       or the cut wanted and the cut given are in different dimensions,
--         (splitting the space into a kind of "matrix").
-- (ii)  The following "plumbing" operators might be useful to implement:
{-
plumb : ∀ {I J K}{P : K -> Set}{f : I -> J -> K}{js : I -> List J} ->
        ∀ is → (All (All P) ∘′ L.map (\ i -> L.map (f i) (js i))) is →
                All (\ i -> All (P ∘′ f i) (js i)) is

plumb⁻¹ : ∀ {I J K}{P : K -> Set}{f : I -> J -> K}{js : I -> List J} ->
        ∀ is →  All (\ i -> All (P ∘′ f i) (js i)) is →
                (All (All P) ∘′ L.map (\ i -> L.map (f i) (js i))) is
-}
-- (iii) I would recommend to be on the lookout for opportunities to
--       use map operations, in order to keep the code tidy.

  recutPair : Recutter (C |+| D)
  recutPair = {!!}

-- After all that hard work, you obtain a recutter for RectCut!

rectRecutter : Recutter RectCut
rectRecutter = recutPair NatCut NatCut natRecutter natRecutter

END OF COMMENT fortrose -}


------------------------------------------------------------------------------
-- Building applications (10 MARKS in total)
------------------------------------------------------------------------------

-- We are almost ready to start managing windows!

-- To get you started, here is a very simple application which you
-- will embellish during the course of the coursework.  If you make
-- sure all holes are commented out, you should be able to run this
-- now! All it does is fill the terminal with a given character
-- (Ctrl-C quits). See the very bottom of this file for instructions
-- how to compile and run the program.

-- You can look up the definition of the type Application in
-- Common.Display, or you can try to get the gist of it from this example
-- application.

rectApp : Char              -- character to display ("state" of the application)
       -> ∀ wh → Application wh  -- an application of *any* screen size
-- To "display", an application must supply a pair of things:
proj₁ (display (rectApp c wh))       -- a matrix of coloured characters
  = replicate (replicate (green - c # black)) -- here, copies of character c
proj₂ (display (rectApp c wh))       -- the cursor position
  = wh -- here, the bottom right corner (= the size of the window)

-- To "react", an application must respond to events, which means giving
-- three things: (i) a new size, (ii) a proof that the new size is correct,
-- (iii) the new incarnation of the application.
-- What's the correct size?

--  When a key is pressed, the screen size must stay the same!
react (rectApp _ wh) (key (char c'))  -- a printable character was typed, so
  = wh , refl , rectApp c' wh  -- *preserve* screen size, switch to typed char
react (rectApp c wh) (key _)  -- another key was pressed, so
  = wh , refl , rectApp c wh  -- do nothing

--  When a resize happens, the screen size must become the demanded size!
react (rectApp c wh) (resize w h)
  = (w , h) , refl , rectApp c (w , h)

{- girvan UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

-----------------------
-- Holes and Overlays
-----------------------

-- If S is some sort of "stuff", indexed by some sort of size, then
-- Holey S is the sized-indexed choice of "some stuff" or "a hole",
-- i.e., the absence of stuff. The point of a hole is to be
-- *transparent* in a display made of multiple layers. Holey is the
-- Maybe monad on (I -C> SET), but it's far too late in the process to
-- be distracted by that now.

data Holey {I : Set}(S : I -> Set)(i : I) : Set where
  hole  : Holey S i
  stuff : S i -> Holey S i


{- ??? 3.39 Show that if you can cut up "stuff", you can also cut up "holey stuff".
   (1 MARK)
-}

-- HINT: Another easy job for those who have done their All homework.

cutHoley : ∀ {I}(C : I <| I)(S : I -> Set) → Cutter C S -> Cutter C (Holey S)
cutHoley = {!!}

-- Now, we fix that we are working with rectangular stuff.

module OVERLAYING (S : ℕ × ℕ -> Set)(cS : Cutter RectCut S) where

  Background : ℕ × ℕ -> Set
  Background = ManyCuts RectCut S       -- Backgrounds are made of stuff.

  Overlay : ℕ × ℕ -> Set
  Overlay = ManyCuts RectCut (Holey S)  -- Overlays can also have holes.


  {- ??? 3.40 Show that you can cut overlays.
     (1 MARK)
  -}

  -- HINT: Specialise an operation you have already developed.

  overlayCutter : Cutter RectCut Overlay
  overlayCutter = {!!}


  {- ??? 3.41 Show that you can superimpose a "front" overlay on a
         "back" overlay, or completely fill in all the holes in an
         overlay, given a background.  In each case, the front overlay
         comes first, the back thing comes second, and the output is
         the combined thing.
     (1 MARK)
  -}

  -- HINT: Sounds like we want to overlay something, no?

  superimpose : ∀ i → Overlay i → Overlay i → Overlay i
  superimpose = {!!}

  backstop : ∀ i → Overlay i → Background i → Background i
  backstop = {!!}

END OF COMMENT girvan -}

{- helensburgh UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

-----------------------------
-- Overlays for Applications
-----------------------------

open OVERLAYING (Matrix ColourChar) matrixCutter

-- For the rest of the exercise, we instantiate the "stuff" in an Overlay
-- to be matrices of coloured characters. That's exactly what we can display
-- in the terminal window.

-- An AppLayer refines the notion of display used in an application.
-- Instead of being a matrix of coloured characters, it is an Overlay,
-- which means it can have *holes*. Later, we'll look at how to superimpose
-- multiple layers.

AppLayer : ℕ × ℕ -> Set
AppLayer = Server AppInterface (λ i → Overlay i × CursorPosition i)


{- ??? 3.42 Reconstruct the simple "rectApp" application as an
       AppLayer, generalising it to allow the colour to be chosen.
       Make it so that pressing ENTER cycles through all the colours.
   (1 MARK)
-}


rectAppLayer : Colour -> Char -> ∀ i → AppLayer i
rectAppLayer = {!!}

{- ??? 3.43 Show how to turn an AppLayer into an Application.
      (1 MARK)
-}

-- Specification:
-- (i)   Any holes in the AppLayer should be filled with white spaces.
-- (ii)  The "stuff" in the AppLayer should display as it is given.
-- (iii) The Application should react as given by the AppLayer.

-- HINTS:
-- (iv)  Note that the type ensures that the Overlay is the size of the
--       screen.
-- (v)   You have already done the hard work by writing "manyCutsMatrix" and
--       "backstop".

runAppLayer : ∀ i → AppLayer i → Application i
runAppLayer = {!!}

-- Congratulations, now you can go and run your fancy new main program
-- at the end of this file!

-----------------------------
-- Applications in a Window
-----------------------------

{- ??? 3.44 Write a function which takes an application of any size
       and displays it as a window at a given position in a screen of any
       size.
      (4 MARKS)
-}

-- Specification:
-- (i)   Any part of the screen not occupied by the application should
--       display as a hole.
-- (ii)  If the application does not fit entirely on the screen, you should
--       display the largest top-left corner of it that does fit.
-- (iii) Trap the arrow keys to move the window without resizing it.
-- (iv)  Trap the shifted arrow keys to resize the window without moving
--       its top left corner.

-- Hints:
-- (v)   You will need to compare positions and sizes in a way that generates
--       the evidence you need to inform cropping and padding. Consider
--       constructing a view which captures "less-or-equal" concretely:
--       Given two numbers, n and m,
--         either m is (n + d) for some d (so n is less than or equal to m),
--         or n is (m + suc d) for some d (so n is greater than m).
--       It may help to repackage the CutCompare "view".
-- (vi)  Padding amounts to filling parts of the screen with holes.
-- (vii) You should find overlayCutter useful.

windowLayer : ∀ (x y : ℕ)          -- left and top coordinates of window
              appWH                -- width and height of window application
           -> AppLayer appWH       -- the application to put in the window
           -> ∀ i → AppLayer i     -- an application which fills the screen
windowLayer = {!!}

-- Congratulations, there is now another new main program for you to
-- try at the end of this file!


------------------------------------------------------------------------------
-- Layering Applications
------------------------------------------------------------------------------

{- ??? 3.45 Write a function which combines two layers into one.
      (1 MARKS)
-}

-- Specification:
-- (i)   The combined display should show the front display, except where it
--       has holes. You should make sure we can see through the holes in the
--       front to the display at the back, showing what's in those places.
-- (ii)  Trap the tab key, making it swap the front and back layers.
-- (iii) All other keystrokes should be handled by the front layer.

-- Hints:
-- (iv)  superimpose
-- (v)   How should "resize" events be handled? What do the types make you do?

twoLayers : (∀ i → AppLayer i → AppLayer i → AppLayer i)
   --              ^^ front     ^^ back      ^^ combined
twoLayers = {!!}

-- You've reached the end, well done! Go and run your new main
-- program, see how it manages two windows, and relax.

END OF COMMENT helensburgh -}


------------------------------------------------------------------------------
-- The Main Program
------------------------------------------------------------------------------

-- Here are a succession of different versions of the  main program to try
-- with the compiler. The first should be ready to run from the beginning.
-- The rest become gradually available as you complete more of the exercise.
-- Of course, you can only try one at a time, keeping the others commented
-- out.

main : IO ⊤
-- The following should work now.
main = appMain (rectApp '*')
-- when you have rectAppLayer working, try this
--main = appMain \ wh -> runAppLayer wh (rectAppLayer green '*' _)
-- when you also have windowLayer working, try this
--main = appMain (λ wh -> runAppLayer wh (windowLayer 2 2 (30 , 20) (rectAppLayer red '@' _) _))
-- when you have everything working, try this
--main = appMain (λ wh -> runAppLayer wh (twoLayers wh (windowLayer 2 2 (30 , 20) (rectAppLayer green '&' _) wh) (windowLayer 12 4 (30 , 20) (rectAppLayer yellow '%' _) wh)))

{-
To compile, move to your CS410 directory and invoke
  agda --compile --ghc-flag "-lncurses" Coursework/Three.agda

To run the program,
  ./Three

Ctrl-C quits the running application.
-}

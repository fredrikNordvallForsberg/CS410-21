{-# OPTIONS --type-in-type #-}
module NowYouTry.DescFreeMonad where

open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Container hiding (refl)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Common.Category

open import Lectures.DataData

open Functor

module _ (U : Set)(El : U -> Set) where

  open DESC U El

  ---------------------------------------------------------------------------
  -- Args is functorial
  ---------------------------------------------------------------------------

  Args-map : (d : Desc) -> {X Y : Set} -> (f : X -> Y) -> Args d X -> Args d Y
  Args-map `⊤ f x = x
  Args-map (`Σ a b) f (x , y) = (x , Args-map (b x) f y)
  Args-map (d `× e) f (x , y) = Args-map d f x , Args-map e f y
  Args-map `X f x = f x

  Args-id : ∀ {A} d → (x : Args d A) → Args-map d (λ x₁ → x₁) x ≡ x
  Args-id `⊤ x = refl
  Args-id (`Σ a b) (x , y) = cong (x ,_) (Args-id (b x) y)
  Args-id (d `× e) (x , y) = cong₂ _,_ (Args-id d x) (Args-id e y)
  Args-id DESC.`X x = refl

  Args-compose : ∀ {X Y Z}{f : X -> Y}{g : Y -> Z} d →
                 (x : Args d X) → Args-map d (λ x₁ → g (f x₁)) x ≡ Args-map d g (Args-map d f x)
  Args-compose `⊤ x = refl
  Args-compose (`Σ a b) (x , y) = cong (x ,_) (Args-compose (b x) y)
  Args-compose (d `× e) (x , y) = cong₂ _,_ (Args-compose d x) (Args-compose e y)
  Args-compose `X x = refl

  ARGS : (d : Desc) -> Functor SET SET
  act (ARGS d) = Args d
  fmap (ARGS d) = Args-map d
  Functor.identity (ARGS d) = ext (Args-id d)
  homomorphism (ARGS d) = ext (Args-compose d)


  ---------------------------------------------------------------------------
  -- Free monads on Args d
  ---------------------------------------------------------------------------

  data FreeM (d : Desc) (X : Set) : Set where
    return : X -> FreeM d X
    layer : Args d (FreeM d X) -> FreeM d X

  -- Crucial point: Args d is obviously strictly positive, so the
  -- above definition is allowed

  mutual

    Args-map' : {c : Desc}(d : Desc) -> {X Y : Set} -> (f : X -> Y) -> Args d (FreeM c X) -> Args d (FreeM c Y)
    Args-map' `⊤ f x = x
    Args-map' (`Σ a b) f (x , y) = (x , Args-map' (b x) f y)
    Args-map' (d `× e) f (x , y) = Args-map' d f x , Args-map' e f y
    Args-map' `X f x = FreeM-map _ f x

    FreeM-map : ∀ {A B : Set} d -> (f : A -> B) -> FreeM d A -> FreeM d B
    FreeM-map d f (return x) = return (f x)
    FreeM-map d f (layer x) = layer (Args-map' d f x)

  mutual

    Args-id' : ∀ {A c} d → (x : Args d (FreeM c A)) → Args-map' d (λ x₁ → x₁) x ≡ x
    Args-id' `⊤ x = refl
    Args-id' (`Σ a b) (x , y) = cong (x ,_) (Args-id' (b x) y)
    Args-id' (d `× e) (x , y) = cong₂ _,_ (Args-id' d x) (Args-id' e y)
    Args-id' DESC.`X x = FreeM-id _ x

    FreeM-id : ∀ {A} d -> (x : FreeM d A) → FreeM-map d (Category.id SET) x ≡ x
    FreeM-id d (return x) = refl
    FreeM-id d (layer x) = cong layer (Args-id' d x)

  mutual
    Args-compose' : ∀ {X Y Z c}{f : X -> Y}{g : Y -> Z} d →
                 (x : Args d (FreeM c X)) → Args-map' d (λ x₁ → g (f x₁)) x ≡ Args-map' d g (Args-map' d f x)
    Args-compose' `⊤ x = refl
    Args-compose' (`Σ a b) (x , y) = cong (x ,_) (Args-compose' (b x) y)
    Args-compose' (d `× e) (x , y) = cong₂ _,_ (Args-compose' d x) (Args-compose' e y)
    Args-compose' `X x = FreeM-map-compose _ x

    FreeM-map-compose : ∀ {X Y Z}{f : X -> Y}{g : Y -> Z} d →
                        (x : FreeM d X) → FreeM-map d (λ x₁ → g (f x₁)) x ≡ FreeM-map d g (FreeM-map d f x)
    FreeM-map-compose d (return x) = refl
    FreeM-map-compose d (layer x) = cong layer (Args-compose' _ x)

  FMF : (d : Desc) -> Functor SET SET
  act (FMF d) = FreeM d
  fmap (FMF d) = FreeM-map d
  Functor.identity (FMF d) = ext (FreeM-id d)
  homomorphism (FMF d) = ext (FreeM-map-compose d)


  ---------------------------------------------------------------------------
  -- Monad structure on FreeM
  ---------------------------------------------------------------------------

  mutual

    Args-map'' : {c : Desc}(d : Desc) -> {X : Set} ->
                 Args d (FreeM c (FreeM c X)) -> Args d (FreeM c X)
    Args-map'' `⊤ x = x
    Args-map'' (`Σ a b) (x , y) = (x , Args-map'' (b x) y)
    Args-map'' (d `× e) (x , y) = Args-map'' d x , Args-map'' e y
    Args-map'' `X x = join _ x

    join : (d : Desc) -> {X : Set} -> FreeM d (FreeM d X) -> FreeM d X
    join d (return x) = x
    join d (layer x) = layer (Args-map'' d x)

  ---------------------------------------------------------------------------
  -- Now you try
  ---------------------------------------------------------------------------

  embed : (d : Desc) -> {X : Set} -> Args d X -> FreeM d X
  embed d x = ?


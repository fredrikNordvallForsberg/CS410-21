{-# OPTIONS --guardedness #-}
module Lectures.LineNumbers where

open import Data.Nat
open import Data.Nat.Show as NS
open import Data.String as String
open import Data.List as List
open import Data.Product
open import Data.Unit.Polymorphic
open import Level as Level

---------------------------------------------------------------------------
-- The IO monad
--------------------------------------------------------------------------

open import IO
import IO.Primitive as Prim

main : Prim.IO ⊤
main = run do
  f <- readFiniteFile "Lectures/LineNumbers.agda"
  let l = lines f
  let numbers = List.map ℕ.suc (upTo (List.length l))
  let newlines = List.map (λ (n , s) → NS.show n String.++ ": " String.++ s) (List.zip numbers l)
  putStrLn (unlines newlines)

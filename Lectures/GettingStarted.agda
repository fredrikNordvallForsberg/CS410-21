module Lectures.GettingStarted where

-- This is a comment

{- And this is a multiline comment.

   Useful key-bindings:

   C-c C-l     load file

 -}

const : {A B : Set} -> A -> B -> A
const = λ a b -> a

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

append : {A : Set} -> List A -> List A -> List A
append [] ys = ys
append (x :: xs) ys = x :: (append xs ys)

data _⊎_ (A B : Set) : Set where
  inj₁ : A -> A ⊎ B
  inj₂ : B -> A ⊎ B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_

swap : {A B : Set} → A × B -> B × A
swap (a , b) = b , a

distribute : {A B C : Set} → A × (B ⊎ C) -> (A × B) ⊎ (A × C)
distribute (a , inj₁ b) = inj₁ (a , b)
distribute (a , inj₂ c) = inj₂ (a , c)

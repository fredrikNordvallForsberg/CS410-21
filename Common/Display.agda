{-# OPTIONS --guardedness #-}
module Common.Display where

open import Data.Nat
open import Data.Bool
open import Data.List as L
open import Data.Vec as V
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Function

open import Foreign.Haskell.Pair
open import IO.Primitive

open import Data.Char
open import Data.String

---------------------------------------------------------------------------
-- COLOURS AND KEY PRESSES
---------------------------------------------------------------------------

-- We're going to be making displays from coloured text.

data Colour : Set where
  black red green yellow blue magenta cyan white : Colour

data ColourChar : Set where
  _-_#_ : (fg : Colour)(c : Char)(bg : Colour) -> ColourChar

-- A matrix is a grid of entries with given number of rows and columns

Matrix : Set -> ℕ × ℕ -> Set
Matrix C (w , h) = Vec (Vec C w) h

-- Describing key presses

data Direction : Set where
  up down left right : Direction

data Modifier : Set where
  normal shift control : Modifier

data Key : Set where
  char       : Char -> Key
  arrow      : Modifier -> Direction -> Key
  enter      : Key
  backspace  : Key
  delete     : Key
  escape     : Key
  tab        : Key

-- window events

data Event : Set where
  key     : (k : Key) -> Event
  resize  : (w h : ℕ) -> Event

{- This type collects the things you're allowed to do with the text window. -}
data Action : Set where
  goRowCol : ℕ -> ℕ -> Action    -- send the cursor somewhere
  sendText : List Char -> Action     -- send some text
  move     : Direction -> ℕ -> Action  -- which way and how much
  fgText   : Colour -> Action
  bgText   : Colour -> Action

-- How to paint a matrix full of coloured text

paintAction : {wh : ℕ × ℕ} -> Matrix ColourChar wh -> List Action
paintAction = V.foldr _ (V.foldr _ g id) [] where
  g : ColourChar -> (List Action -> List Action) -> List Action -> List Action
  g (f - c # b) k as = fgText f ∷ bgText b ∷ sendText (c ∷ []) ∷ k as

{- This is how we compile it all to Haskell -}

{-# FOREIGN GHC import qualified Common.ANSIEscapes as ANSIEscapes #-}
{-# FOREIGN GHC import qualified Common.HaskellSetup as HaskellSetup #-}
{-# COMPILE GHC Colour = data HaskellSetup.Colour (HaskellSetup.Black | HaskellSetup.Red | HaskellSetup.Green | HaskellSetup.Yellow | HaskellSetup.Blue | HaskellSetup.Magenta | HaskellSetup.Cyan | HaskellSetup.White) #-}
{-# COMPILE GHC Direction = data ANSIEscapes.Dir (ANSIEscapes.DU | ANSIEscapes.DD | ANSIEscapes.DL | ANSIEscapes.DR) #-}
{-# COMPILE GHC Modifier = data HaskellSetup.Modifier (HaskellSetup.Normal | HaskellSetup.Shift | HaskellSetup.Control) #-}
{-# COMPILE GHC Key = data HaskellSetup.Key (HaskellSetup.Char | HaskellSetup.Arrow | HaskellSetup.Enter | HaskellSetup.Backspace | HaskellSetup.Delete | HaskellSetup.Escape | HaskellSetup.Tab) #-}
{-# COMPILE GHC Event = data HaskellSetup.Event (HaskellSetup.Key | HaskellSetup.Resize) #-}
{-# COMPILE GHC Action = data HaskellSetup.Action (HaskellSetup.GoRowCol | HaskellSetup.SendText | HaskellSetup.Move | HaskellSetup.FgText | HaskellSetup.BgText) #-}

---------------------------------------------------------------------------
-- APPLICATIONS                                                          --
---------------------------------------------------------------------------

-- Here's a general idea of what it means to be an "application".
-- You need to choose some sort of size-dependent state, then provide these
-- bits and pieces. We need to know how the state is updated according to
-- events, with resizing potentially affecting the state's type. We must
-- be able to paint the state. The state should propose a cursor position.

record Interface (Status : Set) : Set1 where
  constructor interface
  field
    Command  : Status -> Set     -- a.k.a. precondition
    Response : (before : Status)(command : Command before)
              -> Status -> Set  -- a.k.a. postcondition
open Interface public

record Server
  {Status   : Set}
  (Intf     : Interface Status)
  (Display  : Status -> Set)     -- a.k.a. invariant
  (now      : Status)
  : Set
  where
    coinductive
    field
      display : Display now                      -- a server knows the current display, and
      react   : (command : Command Intf now) ->  -- is ready to react to any current command,
                Σ Status λ next ->               -- giving back the next status,
                Response Intf now command next × -- an appropriate response,
                Server Intf Display next         -- and a new server instance
open Server public

-- This is a server interface for applications. The given pair of
-- numbers is the width and height of the screen.

AppInterface : Interface (ℕ × ℕ)
Command  AppInterface wh = Event
Response AppInterface whb (key k)      wha = wha ≡ whb     -- width and height must stay the same
Response AppInterface whb (resize w h) wha = wha ≡ (w , h) -- width and height must be updated

-- a cursor position is always a pair of numbers

CursorPosition : ℕ × ℕ -> Set
CursorPosition wh = ℕ × ℕ

-- an application keeps track of what's on the screen and where the
-- cursor is:

Application : ℕ × ℕ -> Set
Application = Server AppInterface (λ i → Matrix ColourChar i × CursorPosition i)

TopLevel : Set
TopLevel = Σ (ℕ × ℕ) Application

-- How to paint an application, of any width and height

appPaint : TopLevel -> List Action
appPaint (_ , app) = let (p , (x , y)) = display app in
  goRowCol 0 0 ∷ paintAction p L.++ (goRowCol y x ∷ [])

-- The main event handler

appHandler : Event -> TopLevel -> Pair TopLevel (List Action)
appHandler e (wh , app) = let (wh' , _ , app') = react app e in
   ((_ , app') , appPaint (_ , app'))

{- This is the bit of Haskell code that actually talks to the ncurses library -}
postulate
  mainAppLoop : {S : Set} ->             -- program state
    -- INITIALIZER
    S ->                              -- initial state
    -- EVENT HANDLER
    (Event -> S ->                    -- event and state in
     Pair S (List Action)) ->              -- new state and screen actions out
    -- PUT 'EM TOGETHER AND YOU'VE GOT AN APPLICATION!
    IO ⊤
{-# COMPILE GHC mainAppLoop = (\ _ -> HaskellSetup.mainAppLoop) #-}

appMain : (∀ wh → Application wh) -> IO ⊤
appMain app = mainAppLoop ((0 , 0) , app (0 , 0)) appHandler
  -- will get resized dynamically to size of terminal, first thing

------------------------------------------------------------------------
-- CS410 Advanced Functional Programming 2021
--
-- Coursework 2
------------------------------------------------------------------------

module Coursework.Two where

----------------------------------------------------------------------------
-- COURSEWORK 2 -- ISOMORPHIC DEFINITIONS, AND PLAYING AROUND WITH HUTTON'S RAZOR
--
-- VALUE:     30% (divided over 60 marks, ie each mark is worth 0.5%)
-- DEADLINE:  5pm, Monday 1 November (Week 7)
--
-- SUBMISSION: Push your solutions to your own repo. Your last commit
-- before the deadline is your submitted version. However do get in
-- touch if you want to negotiate about extensions.
----------------------------------------------------------------------------

-- HINT: your tasks are labelled with the very searchable tag '???'

-- TIP: When you load this file, you will see lots of open goals. You
-- can focus on one at a time by using comments {- ... -} to switch
-- off the later parts of the file until you get there. Later on you
-- might want to switch off earlier parts to make loading later parts
-- faster (don't forget to switch them back on when you are done!).
-- In fact, the very last section is already commented out for you.

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<ᵇ_)
open import Data.Nat.Properties using (+-identityʳ; +-identityˡ; +-suc; +-comm; +-assoc) renaming (_≟_ to decEqNat)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.Properties using () renaming (_≟_ to decEqBool)
open import Data.List as List using (List; []; _∷_; map)
open import Data.Vec  as Vec  using (Vec;  []; _∷_; map)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; proj₁; proj₂; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String hiding (show; _≤_) renaming (_++_ to _<>_; replicate to repeat)
import Data.Nat.Show as NS using (show)
import Data.Bool.Show as BS using(show)
open import Function using (_∘′_; case_of_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; cong-app; sym; trans; module ≡-Reasoning; subst; isPropositional)
open ≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Nullary.Decidable as RNC

------------------------------------------------------------------------
-- TIME FOR REFLECTION (15 MARKS in total)
------------------------------------------------------------------------

-- In this part, we are considering three different definitions of the
-- less-than relation on natural numbers. Two of them, `A._≤_` and
-- `B._≤_` we have already seen, whereas `C._≤_` is new. We want to
-- show that they are all *isomorphic*, in the following sense:

record _↔_ (A B : Set) : Set where
  field
    to         : A -> B
    from       : B -> A
    left-inverse-of : (x : A) -> from (to x) ≡ x
    right-inverse-of : (y : B) -> to (from y) ≡ y
open _↔_

infix 3 _↔_

-- (There is a similar definition in the standard library's
-- Function.Inverse, but that one is defined in more general terms,
-- and hence more inconvenient to use.)


------------------
module A where
------------------
  infix 4 _≤_

  -- Here is _≤_ defined by pattern matching:

  _≤_ : ℕ -> ℕ -> Set
  zero ≤ m = ⊤
  suc n ≤ zero = ⊥
  suc n ≤ suc m = n ≤ m

  {- ??? 2.1 For practice, show that 17 ≤ 42. Why is this so easy?
     (1 MARK) -}

  17≤42 : 17 ≤ 42
  17≤42 = {!!}

  {- ??? 2.2 Show that this definition is propositional, ie that any two
         proofs of it are equal.
     (1 MARK) -}

  propositional : (n m : ℕ) → isPropositional (n ≤ m)
  propositional = {!!}

------------------
module B where
------------------
  infix 4 _≤_

  -- Here is _≤_ defined inductively:

  data _≤_ : ℕ -> ℕ -> Set where
    z≤n : {n : ℕ} -> zero  ≤ n
    s≤s : {m n : ℕ} -> m ≤ n -> suc m ≤ suc n

  {- ??? 2.3 For comparision, show that 17 ≤ 42 using this definition.
         After you have done it yourself, you could see if Auto can do
         it, too.
     (1 MARK) -}

  17≤42 : 17 ≤ 42
  17≤42 = {!!}


  -- We already proved that this definition was propositional and
  -- transitive, so I'm not going to make you copy-paste the proofs.

  propositional : {n m : ℕ} -> isPropositional (n ≤ m)
  propositional z≤n z≤n = refl
  propositional (s≤s p) (s≤s q) = cong s≤s (propositional p q)

  transitive : ∀ {n m k} → n ≤ m -> m ≤ k -> n ≤ k
  transitive z≤n q = z≤n
  transitive (s≤s p) (s≤s q) = s≤s (transitive p q)

------------------
module C where
------------------
  infix 4 _≤_

  -- Here is a different inductive definition of _≤_. Your task now is
  -- to show that these are all "the same" definition. However you
  -- will see that they still behave different computationally!

  data _≤_ (m : ℕ) : ℕ → Set where
    ≤-refl : m ≤ m
    ≤-step : ∀ {n} → m ≤ n → m ≤ suc n

  {- ??? 2.4 Again, to get a feel for this definition, show that 17 ≤ 42.
     (1 MARK) -}

  17≤42 : 17 ≤ 42
  17≤42 = {!!}

{- ??? 2.5 Show that you can translate back and forth between
       A.≤ and B.≤.
   (2 MARKS) -}

A→B : (n m : ℕ) -> n A.≤ m -> n B.≤ m
A→B = {!!}

B→A : {n m : ℕ} -> n B.≤ m -> n A.≤ m
B→A = {!!}

{- ??? 2.6 Now put together what you have so far to show that
       A.≤ and B.≤ are isomorphic.
   (1 MARK) -}

-- HINT: it is easy to prove equations in propositional types.

-- TIP: if you C-c C-c on an empty result, you get to do a definition
-- by "copattern matching", which is quite convenient: you give a
-- definition for each field in the record.

A↔B : (n m : ℕ) -> n A.≤ m ↔ n B.≤ m
A↔B n m = {!!}

{- ??? 2.7 Now show that you can translate between B.≤ and C.≤.
   (2 MARKS) -}

B→C : {n m : ℕ} -> n B.≤ m -> n C.≤ m
B→C = {!!}

C→B : {n m : ℕ} -> n C.≤ m -> n B.≤ m
C→B = {!!}

{- ??? 2.8 Use the above to get a cheap proof of transitivity
       for C.≤. (First try to do it by hand; it's not so easy!)
   (1 MARK) -}

C-transitive : ∀ {n m k} → n C.≤ m -> m C.≤ k -> n C.≤ k
C-transitive p q = {!!}

{- ??? 2.9 Now show that C.≤ is also propositional, and finish off the
       isomorphism between B.≤ and C.≲.
   (3 MARKS) -}

-- HINT: You might find the following lemma, and its lemma, useful:

¬sucn≤n : {n : ℕ} -> ¬ (suc  n C.≤ n)
¬sucn≤n {n} p = {!!} where
  peel : ∀ {n m} → suc n C.≤ suc m → n C.≤ m
  peel = {!!}

C-propositional : {n m : ℕ} → isPropositional (n C.≤ m)
C-propositional = {!!}

B↔C : (n m : ℕ) -> n B.≤ m ↔ n C.≤ m
B↔C n m = {!!}

{- ??? 2.10 Show that ↔ is transitive, and hence that A.≤ and C.≲ are
       isomorphic.
   (1 MARK) -}

↔-trans : {X Y Z : Set} -> X ↔ Y -> Y ↔ Z -> X ↔ Z
↔-trans p q = {!!}

A↔C : {n m : ℕ} -> n A.≤ m ↔ n C.≤ m
A↔C = {!!}

{- ??? 2.11 Finally, let's show that two randomly chosen large numbers
       are related by C.≤.
   (1 MARK) -}

myProof : 278 C.≤ 13831
myProof = {!!}

-- TERMINOLOGY: this proof method, where we swap between a definition
-- that reduces, and one which we can pattern match on, is usually
-- called "small-scale reflection". It has been involved in all (?)
-- efforts to prove substantial theorems succh as the Four Colour
-- Theorem and the Odd Order Theorem.



------------------------------------------------------------------------
-- EXTENDING HUTTON'S RAZOR (20 MARKS in total)
------------------------------------------------------------------------

-- Here we explore the semantics of a small, but not-so-small-anymore
-- programming language. Compared with Hutton's usual Razor, we have
-- added Booleans with a comparision and if-then-else, and state in
-- the form of one memory cell, which we can read and write.

-----------------------
-- The untyped version
-----------------------

-- We start with an untyped version of the language.

module Untyped where

  data Expr : Set where
    num : ℕ -> Expr
    bit : Bool -> Expr
    get  : Expr
    store_then_ : Expr -> Expr -> Expr
    _+E_ : Expr -> Expr -> Expr
    _*E_ : Expr -> Expr -> Expr
    _<E_ : Expr -> Expr -> Expr
    ifE_then_else_ : Expr -> Expr -> Expr -> Expr

  infix 3 _<E_
  infixl 5 _*E_
  infixl 4 _+E_
  infix 7 store_then_
  infix 8 ifE_then_else_


  -- Here are some example expressions:

  e1 : Expr
  e1 = num 4 +E num 5

  e2 : Expr
  e2 = num 2 *E num 3 +E num 4

  e3 : Expr
  e3 = store (num 7) then (get +E get)

  e4 : Expr
  e4 = store num 0 then (store num 7 then num 5) +E get

  e4' : Expr
  e4' = store num 0 then get +E (store num 7 then num 5)

  e5 : Expr
  e5 = store num 2 then ifE bit false then store num 1 then get else get

  e6 : Expr
  e6 = store num 7 then
         ifE get <E (num 2 *E get)
           then ifE bit true then bit false else bit true
           else bit true

  e7 : Expr
  e7 = ifE get <E num 25 then (get +E num 8) else (get *E num 0)

  e8 : Expr
  e8 = ifE get <E get then (num 2 +E (store get then num 3)) else num 5

  -- Now let us explain how to evaluate such expressions. We will
  -- benefit from some hygiene, so let us define an evalutation monad
  -- to take care of the plumbing for us. We first define values:

  data Val : Set where
    num : ℕ -> Val
    bit : Bool -> Val

  -- Then we can define our monad. Unsurprisingly, it's a combination
  -- of the state monad `Memory -> Memory ×_` (for get and store) and the
  -- Maybe monad (for evaluation errors, eg type errors).

  Memory = Val

  EvalM : Set -> Set
  EvalM A = Memory -> (Memory × Maybe A)

  {- ??? 2.12 Implement the monad operations return and bind.
     (2 MARKS) -}

  return : {A : Set} -> A -> EvalM A
  return = {!!}

  _>>=_ : {A B : Set} -> EvalM A -> (A -> EvalM B) -> EvalM B
  (x >>= f) ρ = {!!}

  _>>_ : {A B : Set} -> EvalM A -> EvalM B -> EvalM B
  x >> y = x >>= (λ _ → y)

  {- ??? 2.13 Prove that they really satisfy the monad laws -- we will
         get back to why they are the way they are later in the class,
         but we can certainly prove this particular instance already
         now.
     (2 MARKS)
  -}

  returnBind : ∀ {A B} → (a : A)(h : A → EvalM B) → return a >>= h ≡ h a
  returnBind = {!!}

  bindReturn : ∀ {A}(m : EvalM A) → ∀ ρ → (m >>= return) ρ ≡ m ρ
  bindReturn = {!!}

  bindBind : ∀ {A B C} (m : EvalM A)(g : A → EvalM B)(h : B → EvalM C) →
             ∀ ρ → ((m >>= g) >>= h) ρ ≡ (m >>= (λ x → g x >>= h)) ρ
  bindBind = {!!}

  {- ??? 2.14 Now implement the specific operations that this monad
         supports: failing, getting and storing.
     (1 MARK) -}

  fail : {A : Set} -> EvalM A
  fail = {!!}

  evalGet : EvalM Val
  evalGet = {!!}

  evalPut : Val -> EvalM ⊤
  evalPut = {!!}

  {- ??? 2.15 State the following properties of evalGet and evalPut as equations, and prove them:

         "evalGetPut": getting a value and then putting it is doing nothing

         "evalPutGet": putting a value and then getting it gives
                       the same result as just returning the value (but the state might change!)
     (1 MARK) -}

  {- HINT: If formulated correctly, these should be very easy to prove. -}

  evalGetPut : {!!}
  evalGetPut = {!!}

  evalPutGet : ∀ (ρ : Memory) → {!!}
  evalPutGet = {!!}


  {- ??? 2.16 Use do-notation to implement evaluation.
     (3 MARKS) -}

  -- HINT: In a do-block, Agda let's you write
  --
  --   (c x) ← e where y → f y
  --
  -- to bind e and match it against the more precise pattern `c x`, using
  -- `f` if `e` didn't match `c x`

  eval : Expr -> EvalM Val
  eval = {!!}

  -- Here are some test cases you can comment in.  Let's only look at
  -- the produced value, and starting with 0 in the store.

  eval' : Expr -> Maybe Val
  eval' e = proj₂ (eval e (num 0))

  {-
  _ : eval' e1 ≡ just (num 9)
  _ = refl

  _ : eval' e2 ≡ just (num 10)
  _ = refl

  _ : eval' e3 ≡ just (num 14)
  _ = refl

  _ : eval' e4 ≡ just (num 12)
  _ = refl

  _ : eval' e4' ≡ just (num 5)
  _ = refl

  _ : eval' e5 ≡ just (num 2)
  _ = refl

  _ : eval' e6 ≡ just (bit false)
  _ = refl

  _ : eval' e7 ≡ just (num 8)
  _ = refl

  _ : eval' e8 ≡ just (num 5)
  _ = refl
  -}


  {- ??? 2.17 Prove the we can prove something about our language, by
         proving the following facts about put and get.
     (1 MARK) -}

  -- HINT: One should be really easy, if you've set up things right.

  getput : ∀ e ρ → eval (store get then e) ρ ≡ eval e ρ
  getput = {!!}

  putget : ∀ e ρ → proj₂ (eval (store e then get) ρ) ≡ proj₂ (eval e ρ)
  putget = {!!}


---------------------
-- The typed version
---------------------

-- Now let's look at a typed variant of the language. It's going to be
-- easier to work with, because we can get rid of the Maybe when
-- evaluating.

module Typed where

  -- We will have the smallest possible number of non-trivial types.

  data Ty : Set where
    nat : Ty
    bool  : Ty

  -- For simplicity, we will only allow getting and storing natural numbers

  data Expr : Ty -> Set where
    num : ℕ -> Expr nat
    bit : Bool -> Expr bool
    get  : Expr nat
    store_then_  : ∀ {t} → Expr nat -> Expr t  -> Expr t
    _+E_ : Expr nat -> Expr nat -> Expr nat
    _*E_ : Expr nat -> Expr nat -> Expr nat
    _<E_ : Expr nat -> Expr nat -> Expr bool
    ifE_then_else_ : ∀ {t} → Expr bool -> Expr t -> Expr t -> Expr t

  infix 3 _<E_
  infixl 5 _*E_
  infixl 4 _+E_
  infix 7 store_then_
  infix 8 ifE_then_else_


  -- Here are the example expressions again, but with types:

  e1 : Expr nat
  e1 = num 4 +E num 5

  e2 : Expr nat
  e2 = num 2 *E num 3 +E num 4

  e3 : Expr nat
  e3 = store num 7 then (get +E get)

  e4 : Expr nat
  e4 = store num 0 then (store num 7 then num 5) +E get

  e4' : Expr nat
  e4' = store num 0 then get +E (store num 7 then num 5)

  e5 : Expr nat
  e5 = store num 2 then ifE bit false then store num 1 then get else get

  e6 : Expr bool
  e6 = store num 7 then
         ifE get <E get +E num 1
           then ifE bit true then bit false else bit true
           else bit true

  e7 : Expr nat
  e7 = ifE get <E num 25 then (get +E num 8) else (get *E num 0)

  e8 : Expr nat
  e8 = ifE get <E get then (num 2 +E (store get then num 3)) else num 5


  -- Here is our refined/simplified notion of evaluation monad.

  Val : Ty -> Set
  Val nat = ℕ
  Val bool = Bool

  Memory = Val nat

  EvalM : Set → Set
  EvalM A = Memory -> (Memory × A)

  {- ??? 2.18 Implement the monad operations for *this* EvalM, and
         confirm that they satisfy the monad laws.
     (1 MARK) -}

  -- COMMENT: You might find this is already easier than before.

  return : {A : Set} → A -> EvalM A
  return = {!!}

  _>>=_ : {A B : Set} → EvalM A -> (A -> EvalM B) -> EvalM B
  (x >>= f) ρ = {!!}

  _>>_ : {A B : Set} → EvalM A -> EvalM B -> EvalM B
  x >> y = x >>= (λ _ → y)

  returnBind : ∀ {A B : Set} → (a : A)(h : A → EvalM B) → (return a) >>= h ≡ h a
  returnBind = {!!}

  bindReturn : ∀ {A : Set} → (m : EvalM A) → ∀ ρ → (m >>= return) ρ ≡ m ρ
  bindReturn = {!!}

  bindBind : ∀ {A B C : Set}(m : EvalM A)(g : A → EvalM B)(h : B → EvalM C) →
             ∀ ρ → ((m >>= g) >>= h) ρ ≡ (m >>= (λ x → (g x) >>= h)) ρ
  bindBind = {!!}

  {- ??? 2.19 Now implement eval again in our glorious typed setting.
         Along the way, implement the get and put operations.
     (3 MARKS) -}

  evalGet : EvalM (Val nat)
  evalGet = {!!}

  evalPut : Val nat -> EvalM ⊤
  evalPut = {!!}

  eval : ∀ {t} → Expr t -> EvalM (Val t)
  eval = {!!}

  -- Note that we now always get a value! No more nothing

  eval₀ : ∀ {t} → Expr t -> Memory -> Val t
  eval₀ e ρ = proj₂ (eval e ρ)

  -- We can also extract the final state, of course

  evalState : ∀ {t} → Expr t -> Memory -> Memory
  evalState e ρ = proj₁ (eval e ρ)

  -- For testing, here are the test cases from above again:

  eval' : ∀ {t} → Expr t -> Val t
  eval' e = eval₀ e 0

  {-
  _ : eval' e1 ≡ 9
  _ = refl

  _ : eval' e2 ≡ 10
  _ = refl

  _ : eval' e3 ≡ 14
  _ = refl

  _ : eval' e4 ≡ 12
  _ = refl

  _ : eval' e4' ≡ 5
  _ = refl

  _ : eval' e5 ≡ 2
  _ = refl

  _ : eval' e6 ≡ false
  _ = refl

  _ : eval' e7 ≡ 8
  _ = refl

  _ : eval' e8 ≡ 5
  _ = refl
  -}



  {- ??? 2.20 Relate the typed and untyped languages by showing how one can
         erase the type information, if one wants.
     (1 MARK) -}

  erase : {t : Ty} → Expr t → Untyped.Expr
  erase = {!!}

  eraseVal : {t : Ty} → Val t → Untyped.Val
  eraseVal = {!!}

  eraseMemory : Memory → Untyped.Memory
  eraseMemory = {!!}

  {- ??? 2.21 Now show that evaluation of typed and their erased
         untyped counterparts agree.  Another way to phrase this is to
         say that we get the same result if we first erase and then
         evaluate, or if we first evaluate, and then erase. Fill in
         the remaining holes in the type to say this, and prove the
         statement.
     (3 MARKS) -}

  welltyped-dont-go-wrong : {t : Ty} → (e : Expr t) → (ρ : Memory) → Untyped.eval {!!} {!!} ≡ ({!!} , just {!!})
  welltyped-dont-go-wrong = {!!}


  {- ??? 2.22 As you will have noticed, there is quite a lot of
         repetition in the _+E_, _*E_ and _<E_ cases. Go back and
         modify the Expr data type to factor out the common elements,
         and update eval accordingly.  Briefly describe the changes
         you have made (or tried to make) here, in a comment.
     (2 MARKS) -}

------------------------------------------------------------------------
-- COMPILING HUTTON'S RAZOR (25 MARKS in total)
------------------------------------------------------------------------

module Compilation where

  open Typed using (Ty; module Ty; Val; Expr; module Expr; eval; eval₀; evalState)  --reimport what we need
  open Ty; open Expr -- get access to the constructors of these data types again
  -- NOTE: if you added new data types in your solution to 2.22, you might want to import them here too


-- Let us now see how we can "compile" our language to a stack-based
-- machine. It's assembly code is given as follows, indexed by lists of
-- the types of the elements of the stack before and after execution:

  data Prog : (before : List Ty) -> (after : List Ty) -> Set where
    -- push to the stack
    PUSH : ∀ {ts t} → Val t → Prog ts (t ∷ ts)
    -- remove top element from stack
    POP  : ∀ {ts t} → Prog (t ∷ ts) ts
    -- arithmetic on the top two elements of the stack
    ADD : ∀ {ts} → Prog (nat ∷ nat ∷ ts) (nat ∷ ts)
    MUL : ∀ {ts} → Prog (nat ∷ nat ∷ ts) (nat ∷ ts)
    -- compare top two elements of the stack
    CMP : ∀ {ts} → Prog (nat ∷ nat ∷ ts) (bool ∷ ts)
    -- load from memory to top of stack
    LOAD : ∀ {ts} → Prog ts (nat ∷ ts)
    -- copy to memory from top of stack
    SAVE : ∀ {ts} → Prog (nat ∷ ts) (nat ∷ ts)
    -- conditionally choose a continuation based on top of stack
    BRANCH : ∀ {ts ts'} → Prog ts ts' -> Prog ts ts' -> Prog (bool ∷ ts) ts'
    -- sequential execution of programs
    _▹_ : ∀ {ts ts' ts''} → Prog ts ts' -> Prog ts' ts'' -> Prog ts ts''
    -- do nothing
    NOOP : ∀ {ts} → Prog ts ts

  infixl 4 _▹_

  {- ??? 2.23 For future debugging but mostly for fun, write a show
         function for our assembly code. Every time you print a BRANCH, you
         should print "-" in front of each block, and then indent the entire
         block 2 spaces.
     (2 MARKS) -}

  -- EXAMPLE: the code corresponding to e5 above should be printed
  {-
     PUSH 7
     SAVE
     LOAD
     LOAD
     PUSH 1
     ADD
     CMP
     BRANCH
     - PUSH true
       BRANCH
       - PUSH false
       - PUSH true
     - PUSH true
  -}

  showIndent : ∀ {ts ts'} → ℕ -> Prog ts ts' -> String
  showIndent = {!!}

  show : ∀ {ts ts'} → Prog ts ts' -> String
  show = showIndent 0

  -- HINT: You can get Agda to print using your show function on a
  --       term by doing C-u C-u C-c C-n; easiest is to write a hole,
  --       eg
  --
  --         test = {!compile e5!}
  --
  --       and then do C-u C-u C-c C-n in the hole.

  {- ??? 2.24 Now show how to compile expressions into programs.
     (2 MARKS) -}

  -- HINT: You will get some help already by the types of the stack
  --       entries, but the real confidence that you have done the
  --       right thing comes later in this file in the form of the run
  --       function, and its soundness theorem.


  compile : ∀ {t ts} → Expr t -> Prog ts (t ∷ ts)
  compile = {!!}

  -- Let us now explain how to actually run our machine code. First we
  -- define what a type-respecting stack is, and hence what a machine
  -- configuration is.

  data Stack :  List Ty -> Set where
    [] : Stack []
    _∷_ : ∀ {ts t} → Val t -> Stack ts -> Stack (t ∷ ts)

  infixr 5 _∷_

  record Conf (ts : List Ty) : Set where
    constructor ⟨_,_⟩
    field
      stack : Stack ts
      memory : ℕ
  open Conf

  {- ??? 2.25 Implement the run function for our programs. Running a
         compiled expression should be the same as evaluating it.
     (2 MARKS) -}

  -- COMMENT: See how conveniently the types make sure that we always
  -- have enough things on the stack?

  run : ∀ {ts ts'} → Prog ts ts' → Conf ts -> Conf ts'
  run = {!!}

  {- ??? 2.26 In fact, *prove* that running a
         compiled expression is the same as evaluating it!
     (4 MARKS) -}

  soundness : ∀ {t ts} → (ρ : ℕ)(xs : Stack ts) → (e : Expr t) ->
              run (compile e) ⟨ xs , ρ ⟩ ≡ ⟨ eval₀ e ρ ∷ xs , evalState e ρ ⟩
  soundness ρ xs p = {!!}

--------------------------
-- An optimising compiler
--------------------------

{- COMMENT ME IN WHEN YOU GET HERE (MY TWIN IS AT THE BOTTOM OF THE FILE)

  -- It's good to be right, but sometimes it is also important to be
  -- fast. Hence let us build an *optimising* compiler from expression
  -- to stack programs. We chose to do this at the level of stack
  -- programs rather than source expressions, as more optimisations
  -- are available to us this way (the flipside however is that we
  -- have lost some of the higher-level meaning of the expressions).

  -- As an example, here is an optimisation that removes NOOP
  -- instructions from programs. (This is not as generous as it seems,
  -- because most likely your compiler have not introduced any
  -- NOOPs. However other optimisations you write might replace more
  -- complicated expressions by NOOP, in which case it is useful to
  -- also be able to remove them.)

  -- We first construct a view of expressions that exposes if they are
  -- a NOOP followed by or preceding another expression. Because we
  -- want to look deeper into our term, we also exposes the
  -- "structural" shapes an expression can have, such as branches and
  -- sequential compositions:

  data NOOP-View : {ts ts' : List Ty} → Prog ts ts' → Set where
    rightNOOP : ∀ {ts ts'} (p : Prog ts ts') → NOOP-View (p ▹ NOOP)
    leftNOOP : ∀ {ts ts'} (p : Prog ts ts') → NOOP-View (NOOP ▹ p)
    branch   : ∀ {ts ts'} (p p' : Prog ts ts') → NOOP-View (BRANCH p p')
    seq : ∀ {ts ts' ts''} (p : Prog ts ts')(p' : Prog ts' ts'') → NOOP-View (p ▹ p')
    other : ∀ {ts ts'} (p : Prog ts ts') → NOOP-View p

  -- Next we define how every program can be seen this way:

  noop-view : ∀ {ts ts'} (p : Prog ts ts') → NOOP-View p
  noop-view (p ▹ NOOP) = rightNOOP p
  noop-view (NOOP ▹ p) = leftNOOP p
  noop-view (BRANCH p p') = branch p p'
  noop-view (p ▹ p') = seq p p'
  noop-view x = other x

  -- Then we can use this view to remove the NOOPs; if the view for
  -- example is `rightNOOP p`, then the original expression was `p ▹
  -- NOOP`.

  myOptimiser1 : ∀ {ts ts'} → Prog ts ts' → Prog ts ts'
  myOptimiser1 p with noop-view p
  ... | rightNOOP p = myOptimiser1 p
  ... | leftNOOP p = myOptimiser1 p
  ... | branch p p' = BRANCH (myOptimiser1 p) (myOptimiser1 p')
  ... | seq p p' = myOptimiser1 p ▹ myOptimiser1 p'
  ... | other .p = p

  -- Next we can prove our optimiser correct. This crucially uses the same view.

  myOptimiser1-correct : ∀ {ts ts'} (p : Prog ts ts') → (c : Conf ts) → run (myOptimiser1 p) c ≡ run p c
  myOptimiser1-correct p c with noop-view p
  ... | rightNOOP p = myOptimiser1-correct p c
  ... | leftNOOP p = myOptimiser1-correct p c
  myOptimiser1-correct .(BRANCH p p') ⟨ true ∷ c , ρ ⟩ | branch p p' = myOptimiser1-correct p ⟨ c , ρ ⟩
  myOptimiser1-correct .(BRANCH p p') ⟨ false ∷ c , ρ ⟩ | branch p p' = myOptimiser1-correct p' ⟨ c , ρ ⟩
  ... | seq p p' rewrite myOptimiser1-correct p c | myOptimiser1-correct p' (run p c) = refl
  ... | other .p = refl

  -- Okay, but before you start writing your own optimisations, let's
  -- set up a framework for applying a whole bunch of optimisations,
  -- repeatedly -- earlier optimisations might enable later ones,
  -- after all.

  {- ??? 2.27 First, to check if an optimisation did something, we
         will need to decide if two programs are equal or not. In
         fact, we will only need the positive evidence when they are
         equal, so it is enough to implement the following:
     (3 MARKS) -}

  -- In case you want to use do-notation for the Maybe monad, here is
  -- the required bind operator:
  _>>=_ = Data.Maybe._>>=_

  eq-ListTy? : (ts ts' : List Ty) → Maybe (ts ≡ ts')
  eq-ListTy? = {!!}

  eq-Prog? : ∀ {a b a' b'} → (p : Prog a b)(p' : Prog a' b') → Maybe (Σ (a ≡ a') λ { refl → Σ (b ≡ b') λ { refl → p ≡ p' } })
  eq-Prog? {a} {b} {a'} {b'} p p' = {!!}

  {- ??? 2.28 Now implement the worker of the optimiser, which takes a
         list of optimisers to run, a maximum number of times to run
         them, and a program to optimise. It should keep applying all
         the optimisers until they no longer have any effect, or the
         maximum number is reached. (Can you think of why the maximum
         number is needed -- are there "correct" optimisers that never
         converge?)
     (2 MARKS) -}

  optimiseWorker :  ∀ {ts ts'} → List (Prog ts ts' → Prog ts ts') → (maxIterations : ℕ) → Prog ts ts' → Prog ts ts'
  optimiseWorker fs maxIters p = {!!}

  {- ??? 2.29 Go forth and optimise! Write as many optimisers as you
         want, and prove each one of them correct. You could consider
         e.g.  arithmetic simplifications, factoring out common parts
         of branches, getput and putput laws, redundant SAVES, ...
         Marks will be awarded based on your average improvement on
         the compilation of the test cases above.

     (10 MARKS)
  -}


  -- Don't forget to add your optimiser to the list here, or it won't be run!
  optimise : ∀ {ts ts'} → Prog ts ts' → Prog ts ts'
  optimise p = optimiseWorker (myOptimiser1 ∷ []) 100000 p

  -- Here is the size function and the improvement measurement, for completeness.

  size : ∀ {ts ts'} → Prog ts ts' → ℕ
  size (PUSH x) = 1
  size POP = 1
  size ADD = 1
  size MUL = 1
  size CMP = 1
  size LOAD = 1
  size SAVE = 1
  size (BRANCH p p') = size p + size p'
  size (p ▹ p') = size p + size p'
  size NOOP = 1

  -- We divide by the size of the original program to calculate the
  -- improvement, so Agda requires us to prove that this is never 0
  size-nonzero : ∀ {ts ts'} → (p : Prog ts ts') → RNC.False (decEqNat (size p) 0)
  size-nonzero (PUSH x) = tt
  size-nonzero POP = tt
  size-nonzero ADD = tt
  size-nonzero MUL = tt
  size-nonzero CMP = tt
  size-nonzero LOAD = tt
  size-nonzero SAVE = tt
  size-nonzero (BRANCH p p')
    = RNC.fromWitnessFalse (λ sp+sp'=0 → RNC.toWitnessFalse (size-nonzero p)
                                                            (Data.Nat.Properties.m+n≡0⇒m≡0 (size p) sp+sp'=0))
  size-nonzero (p ▹ p')
      = RNC.fromWitnessFalse (λ sp+sp'=0 → RNC.toWitnessFalse (size-nonzero p)
                                                            (Data.Nat.Properties.m+n≡0⇒m≡0 (size p) sp+sp'=0))
  size-nonzero NOOP = tt


  averageImprovement = List.sum indivEff / List.length indivEff
    where
    open import Data.Nat.DivMod
    tests : List (Σ[ ts ∈ List Ty ] Σ[ ts' ∈ List Ty ] (Prog ts ts'))
    tests = ([] , _ , compile Typed.e1) ∷
            ([] , _ , compile Typed.e2) ∷
            ([] , _ , compile Typed.e3) ∷
            ([] , _ , compile Typed.e4) ∷
            ([] , _ , compile Typed.e5) ∷
            ([] , _ , compile Typed.e6) ∷
            ([] , _ , compile Typed.e7) ∷
            ([] , _ , compile Typed.e8) ∷ []
    indivEff = List.map (λ (_ , _ , p) → _/_ (100 * (size p ∸ (size (optimise p)))) (size p) {size-nonzero p}) tests

  {- Marks will be awarded as follows: an averageImprovement of
    > 0   is worth   2 MARKS
    > 10  is worth   4 MARKS
    > 15  is worth   5 MARKS
    > 20  is worth   6 MARKS
    > 25  is worth   7 MARKS
    > 30  is worth   8 MARKS
    > 35  is worth   9 MARKS
    > 40  is worth  10 MARKS
  -}

-} -- THIS IS THE CLOSING COMMENT BRACE FOR THE FINAL SECTION

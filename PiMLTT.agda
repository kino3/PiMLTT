module PiMLTT where
-----------------------------------------------------
-- A formalization of 
-- "Programming in Martin-Lof's Type Theory"(PiMLTT)
-----------------------------------------------------

-- Chapter 3 Expressions and definitional equality

open import Data.Nat
open import Data.Char
open import Relation.Binary.Core




-- todo: evaluation 


{-
equiv : {e : Expr} {x : var} → e ≡ ([ x ] e ) [ x ]
equiv = ?
-}

-- arities
data arity : Set where
  O : arity
  _⊗_ : arity → arity → arity
  _↠_ : arity → arity → arity

Variable : arity → Set
Variable α = Char

Value : arity → Set
Value α = ℕ

-- State : Set
-- State = Variable → Value

data Op : Set where
  + : Op
  - : Op
  * : Op



-- 3.8 Definition of what an expression of a certain arity is
data Expr : Set where
  var : {a : arity} → Variable a → Expr -- 1
  const : {a : arity} → Value a → Expr  -- 2
  -- 3
  -- 4 Application

  -- we cannot use '(' and ')' because they were reserved
  --_[_] : { → Expr → Prog -- 3.1 Application
  --[_]_ : Expr → Prog → Prog -- 3.2 Abstraction 
  --_,_ : Prog → Prog → Prog -- 3.3 Combination



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


-- arities
data arity : Set where
  O : arity
  _⊗_ : arity → arity → arity
  _↠_ : arity → arity → arity

{-
Variable : arity → Set
Variable α = Char

Value : arity → Set
Value α = ℕ
-}
Variable : Set
Variable = Char

Value : Set
Value = ℕ

-- State : Set
-- State = Variable → Value

data Op : Set where
  + : Op
  - : Op
  * : Op

-- 3.8 Definition of what an expression of a certain arity is
data Expr : Set where
  var : Variable → Expr
  const : Value → Expr 
  -- we cannot use '(' and ')' because they were reserved
  _[_] : Op → Expr → Expr -- 3.1 Application
  [_]_ : Expr → Expr → Expr -- 3.2 Abstraction 
  _,_ : Expr → Expr → Expr  -- 3.3 Combination

{-
equiv : {e : Expr} {x : Expr} → e ≡ ([ x ] e ) [ x ]
equiv = ?
-}

getArity : Expr → arity
getArity (var x) = O
getArity _ = {!!}

module PiMLTT where
-----------------------------------------------------
-- A formalization of 
-- "Programming in Martin-Lof's Type Theory"(PiMLTT)
-----------------------------------------------------

-- Chapter 3 Expressions and definitional equality

open import Data.Nat
open import Data.Char
open import Relation.Binary.Core

Variable : Set
Variable = Char

Value : Set
Value = ℕ

data Op : Set where
  + : Op
  - : Op
  * : Op

data Expr : Set where
  c : Value → Expr
  v : Variable → Expr
  -- o : Expr → Op → Expr → Expr

-- todo: evaluation 

{-
  _[_] : Op → Expr → Expr -- 3.1 Application
    -- we cannot use '(' and ')' because they were reserved
  [_]_ : var → Expr → Expr -- 3.2 Abstraction 
  _,_ : Expr → Expr → Expr -- 3.3 Combination
-}

{-
equiv : {e : Expr} {x : var} → e ≡ ([ x ] e ) [ x ]
equiv = ?
-}

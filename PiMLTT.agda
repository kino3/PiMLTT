module PiMLTT where
-----------------------------------------------------
-- A formalization of 
-- "Programming in Martin-Lof's Type Theory"(PiMLTT)
-----------------------------------------------------

-- Chapter 3 Expressions and definitional equality

-- arities
data arity : Set where
  O : arity -- instead of 0(zero) 
  _⊗_ : arity → arity → arity
  _↠_ : arity → arity → arity

postulate
  Variable : arity → Set
  Value : Set

{-
record expression : Set₁ where
  field
    a : arity
    e : a → Set
-}
data expression (a : arity) : Set where
  var : Variable a → expression a

data Op : Set where
  + : Op
  - : Op
  * : Op

{-
data Expr : Set where
  var : Variable → Expr
  const : Value → Expr 
  -- we cannot use '(' and ')' because they were reserved
  _[_] : Op → Expr → Expr -- 3.1 Application
  [_]_ : Expr → Expr → Expr -- 3.2 Abstraction 
  _,_ : Expr → Expr → Expr  -- 3.3 Combination
-}
{-
equiv : {e : Expr} {x : Expr} → e ≡ ([ x ] e ) [ x ]
equiv = ?
-}



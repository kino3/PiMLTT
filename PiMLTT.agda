module PiMLTT where
-----------------------------------------------------
-- A formalization of 
-- "Programming in Martin-Lof's Type Theory"(PiMLTT)
-----------------------------------------------------

-- Chapter 3 Expressions and definitional equality

-- 3.6 Arities

-- arities
data arity : Set where
  O : arity -- instead of 0(zero) 
  _⊗_ : arity → arity → arity
  _↠_ : arity → arity → arity

-- 3.8 Definition of what an expression of a certain arity is

postulate
  variable : arity → Set
  value : arity → Set

data expression (α : arity) : Set where
  var : variable α → expression α -- 1 Variables
  const : value α → expression α  -- 2 Primitive constants

-- 3 Defined constants

-- 4 Application
_[_] : {α β : arity} → expression (α ↠ β) → expression α → expression β
d [ a ] = {!!}

-- 5 Abstraction
[_]_ : {α β : arity} → variable α → expression β → expression (α ↠ β)
[ x ] b = {!!}

-- 6 Combination
_,_ : {α₁ α₂ : arity} → expression α₁ → expression α₂ → expression (α₁ ⊗ α₂)
a₁ , a₂ = {!!}

-- 7 Selection




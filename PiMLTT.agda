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

data expression : arity → Set where
  -- 1 Variables
  var : {α : arity} → variable α → expression α 
  -- 2 Primitive constants
  const : {α : arity} → value α → expression α  
  -- 4 Application
  _[_] : {α β : arity} → expression (α ↠ β) → expression α → expression β
  -- 5 Abstraction 
  [_]_ : {α β : arity} → variable α → expression β → expression (α ↠ β) 
  -- 6 Combination
  _,_ : {α₁ α₂ : arity} → expression α₁ → expression α₂ → expression (α₁ ⊗ α₂)

  -- 3 Defined constants
  -- 7 Selection


-- 3.9 Definition of equality between two expressions
-- use :: instead of :
data _≡_::_ : {α : arity} → expression α → expression α → arity → Set where
  var-eq : (α : arity) → {x : variable α} → var x ≡ var x :: α
  const-eq : (α : arity) → {c : value α} → const c ≡ const c :: α
  --def-eq : 

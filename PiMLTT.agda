module PiMLTT where
-----------------------------------------------------
-- A formalization of 
-- "Programming in Martin-Lof's Type Theory"(PiMLTT)
-----------------------------------------------------
open import Data.List

-----------------------------------------------------
-- Chapter 3 Expressions and definitional equality
-----------------------------------------------------

-----------------------------------------------------
-- 3.6 Arities
-----------------------------------------------------

-- arities
data arity : Set where
  O : arity -- instead of 0(zero) 
  add : List arity → arity
  _↠_ : arity → arity → arity

-- syntax sugar of add
_⊗_ : arity → List arity → arity
α ⊗ αl = add (α ∷ αl)

-----------------------------------------------------
-- 3.8 Definition of 
--       what an expression of a certain arity is
-----------------------------------------------------

module Expression (
  variable : arity → Set)(
  value : arity → Set
  ) where

 open import Data.Product using (_×_)
 open import Data.Unit

 mutual

   data expression : arity → Set where
    -- 1 Variables
    var : {α : arity} → variable α → expression α 
    -- 2 Primitive constants
    const : {α : arity} → value α → expression α  
    -- 3 Definied constants
    def-const : {α : arity} → expression α → expression α  
    -- 4 Application
    _[_] : {α β : arity} → expression (α ↠ β) → expression α → expression β
    -- 5 Abstraction 
    [_]_ : {α β : arity} → variable α → expression β → expression (α ↠ β) 
    -- 6 Combination
    mkCombi : {αl : List arity} → expList αl → expression (add αl)

   expList : List arity → Set
   expList [] = ⊤ -- singleton
   expList (α ∷ αl) = expression α × expList αl
 
 _,_ : {α : arity} {αl : List arity} → expression α → expList αl → expression (α ⊗ αl)
 a , al = mkCombi (a Data.Product., al)
   
  -- 7 Selection  

-- 3.9 Definition of equality between two expressions
-- use :: instead of : 
-- TODO:: change ≡
 data _≡_::_ : {α : arity} → expression α → expression α → arity → Set where
  var-eq : (α : arity) → {x : variable α} → var x ≡ var x :: α
  const-eq : (α : arity) → {c : value α} → const c ≡ const c :: α
  --def-eq : 

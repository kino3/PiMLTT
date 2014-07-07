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
 open import Data.Nat

 data definiendum : Set where
  d : ℕ → arity → definiendum

 arity-of : definiendum → arity
 arity-of (d _ a) = a

 mutual

   data expr : arity → Set where
    -- 1 Variables
    var : {α : arity} → variable α → expr α 
    -- 2 Primitive constants
    const : {α : arity} → value α → expr α  
    -- 3 Definied constants
    definien : (def : definiendum) → expr (arity-of def)
     
    -- 4 Application
    _[_] : {α β : arity} → expr (α ↠ β) → expr α → expr β
    -- 5 Abstraction 
    [_]_ : {α β : arity} → variable α → expr β → expr (α ↠ β) 
    -- 6 Combination
    mkCombi : {αl : List arity} → exprList αl → expr (add αl)

   exprList : List arity → Set
   exprList [] = ⊤ -- singleton
   exprList (α ∷ αl) = expr α × exprList αl
 
 -- 6 Combination
 _,_ : {α : arity} {αl : List arity} → expr α → exprList αl → expr (α ⊗ αl)
 a , al = mkCombi (a Data.Product., al)
 -- TODO:: maybe we dont need mkcombi
   
 -- 7 Selection
 -- TODO:: we shouldn't use ℕ since this paper's ℕ start with 1.
 [_]-_ : {α : arity} {αl : List arity} → exprList αl → ℕ → expr α
 [ el ]- zero = {!!}
 [ el ]- suc n = {!!} 
 

-- 3.9 Definition of equality between two expressions
-- use :: instead of : 
 data _≡_::_ : {α : arity} → expr α → expr α → arity → Set where
  var-eq : (α : arity) → {x : variable α} → var x ≡ var x :: α
  const-eq : (α : arity) → {c : value α} → const c ≡ const c :: α
  --def-eq : (α : arity) → {a : value α} → const a ≡ def-const (const a) :: α
  apply-eq : (α β : arity) → {c : value α} → const c ≡ const c :: α

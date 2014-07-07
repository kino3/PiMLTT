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
  d : ℕ → arity → definiendum --TODO why need ℕ?

 arity-of : definiendum → arity
 arity-of (d _ a) = a

 mutual

   data expr : arity → Set where
    -- 1 Variables
    var : {α : arity} → variable α → expr α 

    -- 2 Primitive constants
    const : {α : arity} → value α → expr α  

    -- 3 Definied constants
    def-const : (def : definiendum) → expr (arity-of def)

    -- 4 Application
    -- TODO I did not understand why I cannot use _[_] (parsing error?)
    apply_to_ : {α β : arity} → expr (α ↠ β) → expr α → expr β

    -- 5 Abstraction (lambda)
    <_>_ : {α β : arity} → variable α → expr β → expr (α ↠ β) 

    -- 6 Combination
    _,_ : {α : arity} {αl : List arity} → expr α → exprList αl → expr (α ⊗ αl)

    -- 7 Selection TODO: precise def.
    -- [_]-_ : {α : arity} {αl1 αl2 : List arity} → exprList αl1 × expr α × exprList αl2 → expr α
   
   infixr 10 _,_ -- TODO; right?

   exprList : List arity → Set
   exprList [] = ⊤ -- singleton
   exprList (α ∷ αl) = expr α × exprList αl

-----------------------------------------------------
-- 3.9 Definition of equality between two expressions
-----------------------------------------------------
 data _≡_∶_ : {α : arity} → expr α → expr α → arity → Set where
  -- 1. Variables.
  var-eq : {α : arity} → (x : variable α) → var x ≡ var x ∶ α
  -- 2. Constants.
  const-eq : {α : arity} → (c : value α) → const c ≡ const c ∶ α
  -- 3. Definiendum ≡ Definiens. TODO
  def-eq : {α : arity} {a : expr α} → a ≡ def-const (d {!!} α) ∶ α
  -- 4. Application 1.
  apply-eq : {α β : arity} {a a' : expr (α ↠ β)} {b b' : expr α} 
             → a ≡ a' ∶ (α ↠ β) → b ≡ b' ∶ α 
             → (apply a to b) ≡ (apply a' to b') ∶ β

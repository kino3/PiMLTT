module PiMLTT where
-----------------------------------------------------
-- A formalization of 
-- "Programming in Martin-Lof's Type Theory"(PiMLTT)
-----------------------------------------------------
open import Data.Vec
open import Data.Nat
open import Data.Product using (_×_)
open import Data.Unit

-----------------------------------------------------
-- Chapter 3 Expressions and definitional equality
-----------------------------------------------------

-----------------------------------------------------
-- 3.6 Arities
-----------------------------------------------------

{-
data NEVector (X : Set) : ℕ → Set where
  singleton : X → NEVector X zero
  _⊗_ : {n : ℕ} → X → NEVector X n → NEVector X (suc n)
-}


-- arities
data arity : Set where
  O : arity -- instead of 0(zero) 
  _⊗_ : {n : ℕ} → arity → Vec arity n → arity
  --[[_]] : {n : ℕ} → Vec arity n → arity
  _↠_ : arity → arity → arity

-----------------------------------------------------
-- 3.8 Definition of 
--       what an expression of a certain arity is
-----------------------------------------------------

module Expression (
  variable : arity → Set)(
   value : arity → Set
  ) where


 data definiendum : Set where
  d : ℕ → arity → definiendum --TODO why need ℕ?

 arity-of : definiendum → arity
 arity-of (d _ a) = a

 mutual

   data expr : arity → Set where
    var : {α : arity} → variable α → expr α 
    const : {α : arity} → value α → expr α  
    --def-const : (def : definiendum) → expr (arity-of def)
    apply_to_ : {α β : arity} → expr (α ↠ β) → expr α → expr β
    <_>_ : {α β : arity} → variable α → expr β → expr (α ↠ β) 
    _,_ : {α₁ : arity} {n : ℕ} {α₂αₙ : Vec arity n} 
      → expr α₁ → exprList α₂αₙ → expr (α₁ ⊗ α₂αₙ)
    
   exprList : {n : ℕ} → Vec arity n → Set
   exprList [] = ⊤
   exprList (α ∷ αl) = expr α × exprList αl

 + = expr ((O ⊗ (O ∷ [])) ↠ O)

 -- 7 Selection TODO: precise def.
 -- If a is an expression of arity α₁ ⊗...⊗ αₙ and 1 ≤ i ≤ n, then
 -- (a).i
 -- is an expression of arity αᵢ.
{-
 [_]-_ : {αᵢ α₁ : arity} {n : ℕ} {α₂αₙ : Vec arity n} → expr (α₁ ⊗ α₂αₙ) → ℕ → expr αᵢ
 [ var x ]- i = {!!}
 [ const x ]- i = {!!}
 [ apply a to a₁ ]- i = {!!}
 [ a , x ]- i = {!!}
-}


-----------------------------------------------------
-- 3.9 Definition of equality between two expressions
-----------------------------------------------------
 infix 5 _≡_∶_
 data _≡_∶_ : {α : arity} → expr α → expr α → arity → Set where
  -- 1. Variables.
  var-eq : {α : arity} → (x : variable α) → var x ≡ var x ∶ α
  -- 2. Constants.
  const-eq : {α : arity} → (c : value α) → const c ≡ const c ∶ α
  -- 3. Definiendum ≡ Definiens. TODO
  --def-eq : {α : arity} {a : expr α} → a ≡ def-const (d {!!} α) ∶ α
  -- 4. Application 1.
  apply-eq : {α β : arity} {a a' : expr (α ↠ β)} {b b' : expr α} 
             → a ≡ a' ∶ (α ↠ β) → b ≡ b' ∶ α 
             → (apply a to b) ≡ (apply a' to b') ∶ β

  -- 5. Application 2. (β-rule).

  -- If x is a variable of arity α, a an expression of arity α
  -- b an expression of arity β, then
  -- ((x)b)(a) ≡ b[x := a] : β
  -- provided that no free variables in a becomes bound in b[x := a].

  -- 6. Abstraction 1. (ξ-rule). (\xi)
  ξ-rule : {α β : arity} {x : variable α} {b b' : expr β} 
           → < x > b ≡ < x > b' ∶ α ↠ β
  
  -- 

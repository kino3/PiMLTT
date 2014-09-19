module Arity where
open import Data.Nat
open import Data.Vec

data Arity : Set where
  O : Arity
  _⊗_ : Arity → Arity → Arity --TODO n>=1
  _↠_ : Arity → Arity → Arity

infixr 10 _↠_
infixr 20 _⊗_

-- Example of arities
ex1 = O ↠ O ⊗ O
ex2 = ((O ↠ O) ⊗ O ⊗ O) ↠ O
ex3 = O ⊗ O ⊗ O
-- TODO two arities are equal only if they are syntactically identical.

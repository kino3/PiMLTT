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

length : Arity → ℕ --TODO (this is 0<=length, but 1<=length)
length O = suc zero
length (a1 ⊗ a2) = length a1 + length a2
length (a ↠ b) = suc zero

a = length ex3

open import Data.Fin hiding (_+_;compare)
open import Relation.Nullary
nth : {a : Arity} → Fin (length a) → Arity
nth {O} n = O
nth {a1 ⊗ a2} n with length a1 ≤? (toℕ n)
... | yes p = nth {a2} (reduce≥ n p) 
... | no ¬p = nth {a1} {!!}
nth {a1 ↠ a2} n = a1 ↠ a2
{-
nth [[ as ]] k = nth' as k where
  nth' : {n : ℕ} → (as : Vec Arity n) → Fin (length [[ as ]]) → Arity
  nth' {0} [] zero = O
  nth' {0} [] (suc ())
  nth' {suc n} (a ∷ as) zero = a
  nth' {suc n} (a ∷ as) (suc h) = nth' as h
nth (a ↠ b) _ = a ↠ b
-}

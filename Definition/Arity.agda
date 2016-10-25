module Definition.Arity where
open import Data.Nat

{- P.18 Definition 1 -}
-- 2016-10-25
-- ℕ represents a number of ⊗ which occurs outermost of the expression.
data Arity : ℕ → Set where
  O : Arity 0
  _⊗_ : {a b : ℕ} → Arity a → Arity b → Arity (suc (a + b))
  _↠_ : {a b : ℕ} → Arity a → Arity b → Arity 0

infixr 10 _↠_
infixr 20 _⊗_

-- Example of arities
ex1 : Arity 0
ex1 = O ↠ O ⊗ O

ex2 : Arity 0
ex2 = ((O ↠ O) ⊗ O ⊗ O) ↠ O

ex3 : Arity 2
ex3 = O ⊗ O ⊗ O

data Expression {n : ℕ} : Arity n → Set where
  var : (x : ℕ) → {α : Arity n} → Expression α

x : Expression O
x = var 1

{-
length : {n : ℕ} → Arity n → ℕ
length {n} a = n

a = length ex3

open import Data.Fin hiding (_+_)

nth : {m n : ℕ} → (a : Arity n) → Fin (length a) → Arity m
nth O f = {!!}
nth (a₁ ⊗ a₂) f = {!!}
nth (a₁ ↠ a₂) f = {!!}
-}
{-
nth [[ as ]] k = nth' as k where
  nth' : {n : ℕ} → (as : Vec Arity n) → Fin (length [[ as ]]) → Arity
  nth' {0} [] zero = O
  nth' {0} [] (suc ())
  nth' {suc n} (a ∷ as) zero = a
  nth' {suc n} (a ∷ as) (suc h) = nth' as h
nth (a ↠ b) _ = a ↠ b
-}

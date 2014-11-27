module Arity2 where
open import Data.Nat
open import Data.Vec

-- 2014.11.24
-- new version of arity which always has ℕ as a parameter.

data Arity : ℕ → Set where
  O : Arity (suc zero)
  _⊗_ : {a b : ℕ} → Arity a → Arity b → Arity (a + b) --TODO n>=1
  _↠_ : {a b : ℕ} → Arity a → Arity b → Arity (suc zero)

infixr 10 _↠_
infixr 20 _⊗_

-- Example of arities
ex1 = O ↠ O ⊗ O
ex2 = ((O ↠ O) ⊗ O ⊗ O) ↠ O
ex3 = O ⊗ O ⊗ O
-- TODO two arities are equal only if they are syntactically identical.

length : {n : ℕ} → Arity n → ℕ
length {n} a = n

a = length ex3

open import Data.Fin hiding (_+_)

nth : {m n : ℕ} → (a : Arity n) → Fin (length a) → Arity m
nth O f = {!!}
nth (a₁ ⊗ a₂) f = {!!}
nth (a₁ ↠ a₂) f = {!!}

{-
nth [[ as ]] k = nth' as k where
  nth' : {n : ℕ} → (as : Vec Arity n) → Fin (length [[ as ]]) → Arity
  nth' {0} [] zero = O
  nth' {0} [] (suc ())
  nth' {suc n} (a ∷ as) zero = a
  nth' {suc n} (a ∷ as) (suc h) = nth' as h
nth (a ↠ b) _ = a ↠ b
-}

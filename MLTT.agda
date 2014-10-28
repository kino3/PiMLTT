module MLTT where

open import Data.String
open import Data.Nat
open import Arity

data expr : Arity → Set where
    var : {α : Arity} → String → expr α 
    const : {α : Arity} → ℕ → expr α
    _′_ : {α β : Arity} → expr (α ↠ β) → expr α → expr β
    <_∈_>_ : {β : Arity} → String → (α : Arity) → expr β → expr (α ↠ β) 
    --_,_ : {α : Arity} {n : ℕ} {as : Vec Arity n} → expr α → expr [[ as ]] → expr [[ α ∷ as ]]
    --[_]•_ : {n : ℕ} {α : Arity} → expr α → (k : Fin (length α)) → expr (nth α k)
 --infixr 10 _,_
 --infixl 12 <_∈_>_

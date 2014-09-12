module Basic where

-- ProofSummitでの指摘をふまえ、もういちどArityを素直な定義で試みる

module Arity where
  open import Data.Nat
  open import Data.Vec

  data Arity : Set where
    O : Arity
    _⊗_ : Arity → Arity → Arity --TODO n>=1
    _↠_ : Arity → Arity → Arity

  infixr 10 _↠_
  infixr 20 _⊗_

  ex1 = O ↠ O ⊗ O
  ex2 = ((O ↠ O) ⊗ O ⊗ O) ↠ O
  ex3 = O ⊗ O ⊗ O
  -- two arities are equal only if they are syntactically identical.

  -- 9/12 13:14 restart
  open import Relation.Binary
  

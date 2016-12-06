module Definition.Constant where

open import Definition.Arity

data Const : Arity → Set where
  c : (a : Arity) → Const a 

hoge : Const O
hoge = c O


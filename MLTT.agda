module MLTT where
{-
Arityの定義を当初のもの(論文と同じ定義)
に戻して2014.09から書きなおしているもの。
なぜ論文と異なる定義が必要だったのか思いだすのが主目的。
-}
open import Data.String
open import Data.Nat
open import Arity

data Var : Arity → Set where
  v : {α : Arity} → String → Var α

hoge : Var O
hoge = v "x"

data Expr : Arity → Set where
  var : {α : Arity} → Var α → Expr α 
  const : {α : Arity} → ℕ → Expr α
  -- TODO defined constants
  _[_] : {α β : Arity} → Expr (α ↠ β) → Expr α → Expr β
  <_>_ : {α β : Arity} → Var α → Expr β → Expr (α ↠ β) 
    --_,_ : {α : Arity} {n : ℕ} {as : Vec Arity n} → Expr α → Expr [[ as ]] → Expr [[ α ∷ as ]]
    --[_]•_ : {n : ℕ} {α : Arity} → Expr α → (k : Fin (length α)) → Expr (nth α k)
 --infixr 10 _,_
 --infixl 12 <_∈_>_

c4 = const {O} 4

--Π[_,_] : Expr O → Expr O ↠ O → Expr O

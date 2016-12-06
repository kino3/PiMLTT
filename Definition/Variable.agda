module Definition.Variable where

open import Definition.Arity

data Var : Arity → Set where
  v : (a : Arity) → Var a 

hoge : Var O
hoge = v O

{-
open import Relation.Binary.Core
open import Relation.Nullary --.Core
_=v_ : Decidable {A = Var} _≡_
(l ∈ a) =v (l2 ∈ a2) with a =a a2 | l ≟ l2
(l ∈ a) =v (.l ∈ .a) | yes refl | yes refl = yes refl
(l ∈ a) =v (l2 ∈ a2) | _ | _ = no {!!}
-}

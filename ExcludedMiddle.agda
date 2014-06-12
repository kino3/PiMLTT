module ExcludedMiddle where

-- empty set
data ⊥ : Set where

-- negation
¬_ : Set → Set
¬ A = A → ⊥

infixl 20 ¬_
infix  10 _∨_

open import Data.Sum

-- or operator
_∨_ : Set → Set → Set
A ∨ B = A ⊎ B

em : (A : Set) → A ∨ ¬ A
em A = {!!} -- cannot solve

doubleNeg : {A : Set} → A → ¬ ¬ A
doubleNeg = λ a neg-a → neg-a a

doubleNeg2 : {A : Set} → ¬ ¬ A → A
doubleNeg2 = λ x → {!!} -- cannot solve

nnem : (A : Set) → (¬ ¬ A) ∨ (¬ ¬ ¬ A)
nnem A = [ {!!} , {!!} ]′ {!!}



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

nnem : (A : Set) → (¬ ¬ A) ∨ (¬ ¬ ¬ A)
nnem A = inj₁ (doubleNeg {!!})



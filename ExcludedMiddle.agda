module ExcludedMiddle where

-- empty set
data ⊥ : Set where

-- negation
¬_ : Set → Set
¬ A = A → ⊥

infixl 20 ¬_
infix  10 _∨_

open import Data.Sum
open import Data.Product

-- or operator
_∨_ : Set → Set → Set
A ∨ B = A ⊎ B

-- and operator
_∧_ : Set → Set → Set
A ∧ B = A × B

em : (A : Set) → A ∨ ¬ A
em A = inj₁ {!!} -- cannot solve

W-neg-intro : {A : Set} → A → ¬ ¬ A
W-neg-intro a neg-a = neg-a a

W-neg-intro2 : {A : Set} → ¬ A → ¬ ¬ ¬ A
W-neg-intro2 neg-a neg2-a = neg2-a neg-a

W-neg-elim : {A : Set} → ¬ ¬ A → A
W-neg-elim neg2-a = {!!} -- cannot solve

W-neg-elim2 : {A : Set} → ¬ ¬ ¬ A → ¬ A
W-neg-elim2 neg3-a = λ a → neg3-a (λ neg-a → neg-a a)

nnem : (A : Set) → (¬ ¬ A) ∨ (¬ ¬ ¬ A)
nnem A = {!!}

nnem2 : (A : Set) → (¬ ¬ A) ∨ (¬ A)
nnem2 A = {!!}

prop1 : {A : Set} → ¬ A → (¬ ¬ ¬ A) ∨ (¬ ¬ ¬ ¬ A)
prop1 neg-a = inj₁ (W-neg-intro2 neg-a)

prop2 : {A : Set} → ¬ ¬ A → (¬ ¬ ¬ A) ∨ (¬ ¬ ¬ ¬ A)
prop2 neg2-a = inj₂ (W-neg-intro2 neg2-a)

nnnem : (A : Set) → (¬ ¬ ¬ A) ∨ (¬ ¬ ¬ ¬ A)
nnnem A = [ prop1 , prop2 ]′ {!!}


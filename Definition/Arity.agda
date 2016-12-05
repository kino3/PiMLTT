module Definition.Arity where

open import Data.Nat hiding (_⊔_)
open import Data.Vec
open import Relation.Binary.Core
open import Data.Sum
open import Data.Product
open import Data.Fin

-- 3.6 Arities
data Arity : Set where
  [[_]] : {n : ℕ} → Vec Arity n → Arity
  _↠_   : Arity → Arity → Arity
infixr 8 _↠_

O : Arity
O = [[ [] ]]

_⊗_ : Arity → Arity → Arity
a ⊗ [[ xs ]] = [[ a ∷ xs ]]
a ⊗ (b ↠ c) = [[ a ∷ b ↠ c ∷ [] ]]

{-
congA : {n m : ℕ} {x y : Arity} {xs : Vec Arity n} {ys : Vec Arity m}
 → x ≡ y → [[ xs ]] ≡ [[ ys ]] → [[ x ∷ xs ]] ≡ [[ y ∷ ys ]]
congA refl refl = refl

congA2 : {x1 y1 x2 y2 : Arity}
 → x1 ≡ y1 → x2 ≡ y2 → x1 ↠ x2 ≡ y1 ↠ y2
congA2 refl refl = refl

open import Relation.Binary
open import Relation.Nullary --.Core
open import Function using (_∘_)
open import Data.Empty
_=a_ : Decidable {A = Arity} _≡_
[[ [] ]] =a [[ [] ]] = yes refl
[[ [] ]] =a [[ x ∷ x₁ ]] = no (λ ())
[[ x ∷ x₁ ]] =a [[ [] ]] = no (λ ())
[[ x ∷ xs ]] =a [[ y ∷ ys ]] with x =a y | [[ xs ]] =a [[ ys ]]
... | yes p1 | yes p2 = yes (congA p1 p2)
... | yes x=y | no xs≠ys = no {!!}
... | no ¬p | yes p = no {!!}
... | no ¬p | no ¬p₁ = no {!!}
[[ x ]] =a (a2 ↠ a3) = no (λ ())
(a1 ↠ a2) =a [[ x ]] = no (λ ())
(a1 ↠ a2) =a (a3 ↠ a4) with a1 =a a3 | a2 =a a4 
... | yes p1 | yes p2 = yes (congA2 p1 p2)
... | _ | _ = no {!!}
-}

Thm : -- justification of the def. of ⊗
 ∀ (a : Arity) →
 a ≡ O ⊎
 (Σ[ b ∈ Arity ] Σ[ c ∈ Arity ] a ≡ b ⊗ c) ⊎
 (Σ[ b ∈ Arity ] Σ[ c ∈ Arity ] a ≡ b ↠ c)
Thm [[ [] ]] = inj₁ refl
Thm [[ x ∷ xs ]] = inj₂ (inj₁ (x , ([[ xs ]] , refl)))
Thm (a1 ↠ a2) = inj₂ (inj₂ (a1 , (a2 , refl)))

length : Arity → ℕ
length [[ as ]] = ln as where
  ln : {n : ℕ} → Vec Arity n → ℕ
  ln {n} _ = suc n
length (a ↠ b) = suc zero

nth : (a : Arity) → Fin (length a) → Arity
nth [[ as ]] k = nth' as k where
  nth' : {n : ℕ} → (as : Vec Arity n) → Fin (length [[ as ]]) → Arity
  nth' {0} [] zero = O
  nth' {0} [] (suc ())
  nth' {suc n} (a ∷ as) zero = a
  nth' {suc n} (a ∷ as) (suc h) = nth' as h
nth (a ↠ b) _ = a ↠ b

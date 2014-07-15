module PiMLTT where
open import Data.Nat
open import Data.Fin
open import Data.String
open import Data.Vec
open import Data.Sum
open import Data.Product
open import Relation.Binary.Core renaming (_≡_ to _≣_)

data arity : Set where
  [[_]] : {n : ℕ} → Vec arity n → arity
  _↠_ : arity → arity → arity
infixr 8 _↠_
O : arity
O = [[ [] ]]
_⊗_ : arity → arity → arity
a ⊗ [[ xs ]] = [[ a ∷ xs ]]
a ⊗ (b ↠ c) = [[ a ∷ b ↠ c ∷ [] ]]


Thm : -- justification of the def. of ⊗
 ∀ (a : arity) →
 a ≣ O ⊎
 (Σ[ b ∈ arity ] Σ[ c ∈ arity ] a ≣ b ⊗ c) ⊎
 (Σ[ b ∈ arity ] Σ[ c ∈ arity ] a ≣ b ↠ c)
Thm [[ [] ]] = inj₁ refl
Thm [[ x ∷ xs ]] = inj₂ (inj₁ (x , ([[ xs ]] , refl)))
Thm (a1 ↠ a2) = inj₂ (inj₂ (a1 , (a2 , refl)))

length : arity → ℕ
length [[ as ]] = ln as where
  ln : {n : ℕ} → Vec arity n → ℕ
  ln {n} _ = suc n
length (a ↠ b) = suc zero

nth : (a : arity) → Fin (length a) → arity
nth [[ as ]] k = nth' as k where
  nth' : {n : ℕ} → (as : Vec arity n) → Fin (length [[ as ]]) → arity
  nth' {0} [] zero = O
  nth' {0} [] (suc ())
  nth' {suc n} (a ∷ as) zero = a
  nth' {suc n} (a ∷ as) (suc h) = nth' as h
nth (a ↠ b) _ = a ↠ b

module Expression (Var : arity → Set) (Val : arity → Set) where
 open import Data.Product using (_×_)
 open import Data.Unit
 open import Data.Nat
 data expr : arity → Set where
    var : {α : arity} → String → expr α 
    const : {α : arity} → Val α → expr α  
    _′_ : {α β : arity} → expr (α ↠ β) → expr α → expr β
    <_∈_>_ : {β : arity} → String → (α : arity) → expr β → expr (α ↠ β) 
    _,_ : {α : arity} {n : ℕ} {as : Vec arity n} →
      expr α → expr [[ as ]] → expr [[ α ∷ as ]]
    [_]•_ : {n : ℕ} {a : arity} →
      expr a → (k : Fin (length a)) → expr (nth a k)
 infixr 10 _,_
 infixl 12 <_∈_>_

 infix 5 _≡_∈_
 data _≡_∈_ : {α : arity} → expr α → expr α → arity → Set where
   var-eq : {α : arity} → {x : String} → var {α} x ≡ var x ∈ α
   const-eq : {α : arity} → (c : Val α) → const c ≡ const c ∈ α
   apply-eq : {α β : arity} {a0 a1 : expr (α ↠ β)} {b0 b1 : expr α} →
     a0 ≡ a1 ∈ (α ↠ β) → b0 ≡ b1 ∈ α →
     (a0 ′ b0) ≡ (a1 ′ b1) ∈ β
   ξ-rule : {α β : arity} {x : String} {b b' : expr β} →
     b ≡ b' ∈ β →  < x ∈ α > b ≡ < x ∈ α > b' ∈ α ↠ β


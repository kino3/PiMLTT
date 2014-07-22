module PiMLTT where
open import Data.Nat
open import Data.Fin
open import Data.String
open import Data.Vec
open import Data.Sum
open import Data.Product
open import Relation.Binary.Core renaming (_≡_ to _≣_)

-- 3.6 Arities
-- Definition 1
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

module Expression (Val : arity → Set) where
 data expr : arity → Set where
    var : {α : arity} → String → expr α 
    const : {α : arity} → Val α → expr α
    _′_ : {α β : arity} → expr (α ↠ β) → expr α → expr β
    <_∈_>_ : {β : arity} → String → (α : arity) → expr β → expr (α ↠ β) 
    _,_ : {α : arity} {n : ℕ} {as : Vec arity n} →
      expr α → expr [[ as ]] → expr [[ α ∷ as ]]
    [_]•_ : {n : ℕ} {α : arity} →
      expr α → (k : Fin (length α)) → expr (nth α k)
 infixr 10 _,_
 infixl 12 <_∈_>_
 open import Data.List
 assign' : {α β : arity} → expr β → List (String × arity) → String → expr α → expr β
 assign' (var x) lv v e = {!!}
 assign' (const x) lv v e = const x
 assign' (x ′ x₁) lv v e = {!!}
 assign' (< x ∈ α > x₁) lv v e = {!!} -- α-conv
 assign' (x , x₁) lv v e = {!!}
 assign' ([ x ]• k) lv v e = {!!}

 assign : {α β : arity} → expr β → String → expr α → expr β
 assign e v e' = assign' e [] v e'

 -- substitution
 _[_≔_] : {α β : arity} → expr β → String → expr α → expr β
 _[_≔_] {α} {β} d x e = (< x ∈ α > d) ′ e
 -- TODO provided that no free variables in a becomes bound in b [ x ≔ a ].
 infix 5 _≡_∈_
 data _≡_∈_ : {α : arity} → expr α → expr α → arity → Set where
   var-eq : {α : arity} → {x : String} → var {α} x ≡ var x ∈ α
   const-eq : {α : arity} → (c : Val α) → const c ≡ const c ∈ α
   apply-eq : {α β : arity} {a a' : expr (α ↠ β)} {b b' : expr α} →
     a ≡ a' ∈ (α ↠ β) → b ≡ b' ∈ α →
     (a ′ b) ≡ (a' ′ b') ∈ β
   β-rule : {α β : arity} {x : String} {b : expr β} {a : expr α}
      → (< x ∈ α > b) ′ a ≡ b [ x ≔ a ] ∈ β 
   ξ-rule : {α β : arity} {x : String} {b b' : expr β} →
     b ≡ b' ∈ β →  < x ∈ α > b ≡ < x ∈ α > b' ∈ α ↠ β
   -- α-rule

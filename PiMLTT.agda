module PiMLTT where
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Data.String
open import Data.Vec
open import Data.Sum
open import Data.Product
open import Relation.Binary.Core renaming (_≡_ to _≣_)

{-
以下は標準ライブラリからの引用。
これをPiMLTT.agdaで改めて定義していた？

open import Data.List using (List)
open import Level hiding (suc;zero)
data All {a p} {A : Set a}
         (P : A → Set p) : List A → Set (p ⊔ a) where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : All P xs) → All P (x ∷ xs)
-}


-- 3.6 Arities
-- Definition 1
data Arity : Set where
  [[_]] : {n : ℕ} → Vec Arity n → Arity
  _↠_ : Arity → Arity → Arity
infixr 8 _↠_
O : Arity
O = [[ [] ]]
_⊗_ : Arity → Arity → Arity
a ⊗ [[ xs ]] = [[ a ∷ xs ]]
a ⊗ (b ↠ c) = [[ a ∷ b ↠ c ∷ [] ]]

Thm : -- justification of the def. of ⊗
 ∀ (a : Arity) →
 a ≣ O ⊎
 (Σ[ b ∈ Arity ] Σ[ c ∈ Arity ] a ≣ b ⊗ c) ⊎
 (Σ[ b ∈ Arity ] Σ[ c ∈ Arity ] a ≣ b ↠ c)
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

module Expression (Val : Arity → Set) where
 data expr : Arity → Set where
    var : {α : Arity} → String → expr α 
    const : {α : Arity} → Val α → expr α
    _′_ : {α β : Arity} → expr (α ↠ β) → expr α → expr β
    <_∈_>_ : {β : Arity} → String → (α : Arity) → expr β → expr (α ↠ β) 
    _,_ : {α : Arity} {n : ℕ} {as : Vec Arity n} →
      expr α → expr [[ as ]] → expr [[ α ∷ as ]]
    [_]•_ : {n : ℕ} {α : Arity} →
      expr α → (k : Fin (length α)) → expr (nth α k)
 infixr 10 _,_
 infixl 12 <_∈_>_
 open import Data.List
 assign' : {α β : Arity} → expr β → List (String × Arity) → String → expr α → expr β
 assign' (var x) lv v e = {!!}
 assign' (const x) lv v e = const x
 assign' (x ′ x₁) lv v e = {!!}
 assign' (< x ∈ α > x₁) lv v e = {!!} -- α-conv
 assign' (x , x₁) lv v e = {!!}
 assign' ([ x ]• k) lv v e = {!!}

 assign : {α β : Arity} → expr β → String → expr α → expr β
 assign e v e' = assign' e [] v e'

 -- substitution
 _[_≔_] : {α β : Arity} → expr β → String → expr α → expr β
 _[_≔_] {α} {β} d x e = (< x ∈ α > d) ′ e
 -- TODO provided that no free variables in a becomes bound in b [ x ≔ a ].
 infix 5 _≡_∈_
 data _≡_∈_ : {α : Arity} → expr α → expr α → Arity → Set where
   var-eq : {α : Arity} → {x : String} → var {α} x ≡ var x ∈ α
   const-eq : {α : Arity} → (c : Val α) → const c ≡ const c ∈ α
   apply-eq : {α β : Arity} {a a' : expr (α ↠ β)} {b b' : expr α} →
     a ≡ a' ∈ (α ↠ β) → b ≡ b' ∈ α →
     (a ′ b) ≡ (a' ′ b') ∈ β
   β-rule : {α β : Arity} {x : String} {b : expr β} {a : expr α}
      → (< x ∈ α > b) ′ a ≡ b [ x ≔ a ] ∈ β 
   ξ-rule : {α β : Arity} {x : String} {b b' : expr β} →
     b ≡ b' ∈ β →  < x ∈ α > b ≡ < x ∈ α > b' ∈ α ↠ β
   -- α-rule

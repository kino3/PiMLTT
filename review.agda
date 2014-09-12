module review where
-- ひさびさなので写経する

module Arity where
  open import Data.Nat
  open import Data.Vec

  data Arity : Set where
   [[_]] : {n : ℕ} → Vec Arity n → Arity
   _↠_ : Arity → Arity → Arity

  O : Arity
  O = [[ [] ]]

  _⊗_ : Arity → Arity → Arity
  a ⊗ [[ as ]] = [[ a ∷ as ]]
  a ⊗ (b ↠ c)  = [[ a ∷ b ↠ c ∷ [] ]]

  open import Relation.Binary.Core
  open import Data.Sum
  open import Data.Product using (Σ; _,_; Σ-syntax)

  theorem : -- justification of the def. of ⊗
    ∀ (a : Arity) → 
     a ≡ O ⊎
     (Σ[ b ∈ Arity ] Σ[ c ∈ Arity ] a ≡ b ⊗ c) ⊎
     (Σ[ b ∈ Arity ] Σ[ c ∈ Arity ] a ≡ b ↠ c)
  theorem [[ [] ]] = inj₁ refl
  theorem [[ x ∷ xs ]] = inj₂ (inj₁ (x , [[ xs ]] , refl))
  theorem (a1 ↠ a2) = inj₂ (inj₂ (a1 , a2 , refl))

  length : Arity → ℕ
  length [[ [] ]] = suc zero
  length [[ x ∷ xs ]] = suc (length [[ xs ]])
  length (a1 ↠ a2) = suc zero

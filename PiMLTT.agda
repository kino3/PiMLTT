module PiMLTT where

module Arity where
  open import Data.Nat hiding (_⊔_)
  open import Data.Vec
  open import Relation.Binary.Core renaming (_≡_ to _≣_)
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

open Arity

module Expression (Val : Arity → Set) where
 open import Data.Nat using (ℕ)
 open import Data.String
 open import Data.Vec
 open import Data.Fin
 open import Data.Product
 open import Data.Bool

 -- Variables.
 {-
 record Var (a : Arity) : Set where
   field
     Label : String
 -}

 -- Constants. TODO: use this definition instead of Val
 data Const : Arity → Set where

 data Expr : Arity → Set where
    var    : {α : Arity} → String → Expr α 
    const  : {α : Arity} → Val α → Expr α
    -- TODO def-const
    _′_    : {α β : Arity} → Expr (α ↠ β) → Expr α → Expr β
    <_∈_>_ : {α β : Arity} → String → (α : Arity) → Expr β → Expr (α ↠ β) 
    _,_    : {α : Arity} {n : ℕ} {as : Vec Arity n} →
               Expr α → Expr [[ as ]] → Expr [[ α ∷ as ]]
    [_]•_  : {α : Arity} →
               Expr α → (k : Fin (length α)) → Expr (nth α k)
 infixr 10 _,_
 infixl 12 <_∈_>_

 open import Data.List

 free-variables : {β : Arity} → Expr β → List (String × Arity)
 free-variables {β} (var x) = (x , β) ∷ []
 free-variables (const x)   = []
 free-variables (a↠b ′ a)   = free-variables a
 free-variables (< x ∈ a > e) = dropWhile (λ v → proj₁ v == x) (free-variables e)
 free-variables (a , as)    = free-variables a Data.List.++ free-variables as
 free-variables ([ e ]• k)  = free-variables e
 -- TODO think duplication?
 fv = free-variables

 postulate
  _has_ : {α β : Arity} → Expr α → String → Bool
  _is-in_as-free-var : {β : Arity} → String → Expr β → Bool
  next : String → String
  replace : {α : Arity} → Expr α → String → Expr α

 α-conv : {α : Arity} → Expr α → String → Expr α
 --α-conv (< x ∈ a > e) new = < new ∈ a > {!!} -- α-conv is used just this case.
 α-conv (< x ∈ a > e) new = < {!!} ∈ {!!} > {!!}
 α-conv expr new = expr -- other case

 assign' : {α β : Arity} → Expr β → 
             List (String × Arity) → String → Expr α → Expr β
 assign' (var x) [] v e with x == v
 ... | true = {!!} -- e? but arity is different
 ... | false = var x
 assign' (const x) [] v e  = const x
 assign' (a↠b ′ a) [] v e  = {!!} -- a↠b ′ (assign' a (fv e) v e)
 assign' (< x ∈ a > b) [] v e with x == v
 ... | true  = < x ∈ a > b
 ... | false with b has v
 ... | false = < x ∈ a > b
 ... | true with x is-in e as-free-var
 ... | true = assign' (α-conv (< x ∈ a > b) (next x)) [] v e -- maybe not terminated
 ... | false = < x ∈ a > assign' b [] v e
 assign' (a , as)  [] v e   = assign' a [] v e , assign' as [] v e
 assign' ([ a ]• i) [] v e  = [ assign' a [] v e ]• i
 assign' b (x ∷ xs) v e     = {!!} --TBD

 -- substitution
 _[_≔_] : {α β : Arity} → Expr β → String → Expr α → Expr β
 _[_≔_] {α} {β} b v e = assign' b [] v e

{-
 infix 5 _≡_∈_
 data _≡_∈_ : {α : Arity} → Expr α → Expr α → Arity → Set where
   var-eq   : {α : Arity} → {x : String} → var {α} x ≡ var x ∈ α
   const-eq : {α : Arity} → (c : Val α) → const c ≡ const c ∈ α
   -- TODO: def-eq
   apply-eq : {α β : Arity} {a a' : Expr (α ↠ β)} {b b' : Expr α} →
                a ≡ a' ∈ (α ↠ β) → b ≡ b' ∈ α →
                (a ′ b) ≡ (a' ′ b') ∈ β
   β-rule   : {α β : Arity} {x : String} {b : Expr β} {a : Expr α} → 
                (< x ∈ α > b) ′ a ≡ b [ x ≔ a ] ∈ β 
   ξ-rule   : {α β : Arity} {x : String} {b b' : Expr β} →
               b ≡ b' ∈ β → < x ∈ α > b ≡ < x ∈ α > b' ∈ α ↠ β
   -- α-rule
-}

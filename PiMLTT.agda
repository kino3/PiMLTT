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

 data Expr : Arity → Set where
    var    : {α : Arity} → String → Expr α 
    const  : {α : Arity} → Val α → Expr α
    -- TODO def-const
    _′_    : {α β : Arity} → Expr (α ↠ β) → Expr α → Expr β
    <_∈_>_ : {β : Arity} → String → (α : Arity) → Expr β → Expr (α ↠ β) 
    _,_    : {α : Arity} {n : ℕ} {as : Vec Arity n} →
               Expr α → Expr [[ as ]] → Expr [[ α ∷ as ]]
    [_]•_  : {α : Arity} →
               Expr α → (k : Fin (length α)) → Expr (nth α k)
 infixr 10 _,_
 infixl 12 <_∈_>_

 open import Data.List
 open import Data.Bool
 assign' : {α β : Arity} → Expr β → 
             List (String × Arity) → String → Expr α → Expr β
 assign' (var str)      [] v e with str == v
 ... | true  = {!!} 
 ... | false = var str
 assign' (const b)      [] v e = const b
 assign' (d ′ a)        [] v e = d ′ (assign' a [] v e)
 assign' (< x ∈ α > b)  [] v e with x == v -- = {!!} -- α-conv
 ... | true  = {!!} -- we need α-conversion? which change x to another letter.
 ... | false = (< v ∈ {!!} > (< x ∈ α > b)) ′ e
 assign' (a , as)       [] v e = assign' a [] v e , assign' as [] v e
 assign' ([ a ]• i)     [] v e = [ assign' a [] v e ]• i
 assign' x        (y ∷ ys) v e = {!!}

 hoge : List (String × Arity)
 hoge = ("x" , O) ∷ ("y" ,  O) ∷ []

 -- substitution
 _[_≔_] : {α β : Arity} → Expr β → String → Expr α → Expr β
 _[_≔_] {α} {β} b x a = assign' b [] x a
 -- TODO provided that no free variables in a becomes bound in b [ x ≔ a ].

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

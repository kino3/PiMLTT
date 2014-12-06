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
  
  {-
  open import Relation.Binary
  open import Relation.Nullary.Core
  _=a_ : Decidable {A = Arity} _≣_
  [[ [] ]] =a [[ [] ]] = yes refl
  [[ [] ]] =a [[ x ∷ x₁ ]] = no (λ ())
  [[ x ∷ x₁ ]] =a [[ [] ]] = no (λ ())
  [[ x ∷ xs ]] =a [[ y ∷ ys ]] = {!!}
  [[ x ]] =a (a2 ↠ a3) = no (λ ())
  (a1 ↠ a2) =a [[ x ]] = no (λ ())
  (a1 ↠ a2) =a (a3 ↠ a4) with a1 =a a3 | a2 =a a4
  ... | yes p1 | yes p2 = yes {!!}
  ... | _ | _ = {!!}
  -}

  open import Data.Bool
  _=a_ : Arity → Arity → Bool
  [[ [] ]] =a [[ [] ]] = true
  [[ [] ]] =a [[ x ∷ x₁ ]] = false
  [[ x ∷ x₁ ]] =a [[ [] ]] = false
  [[ x ∷ xs ]] =a [[ y ∷ ys ]] with x =a y
  ... | true = [[ xs ]] =a [[ ys ]]
  ... | false = false
  [[ x ]] =a (a2 ↠ a3) = false
  (a1 ↠ a2) =a [[ x ]] = false
  (a1 ↠ a2) =a (a3 ↠ a4) = a1 =a a3 ∧ a2 =a a4
  
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

module Var where
 open import Data.String
 open import Data.Bool

 record Var : Set where
   constructor _∈_
   field
     l : String
     a : Arity

 hoge : Var
 hoge = "a" ∈ O

 _=v_ : Var → Var → Bool
 (l1 ∈ a1) =v (l2 ∈ a2) = (l1 == l2) ∧ a1 =a a2

module Expression (Val : Arity → Set) where
 open import Data.Nat using (ℕ)
 open import Data.String
 open import Data.Vec hiding (_∈_)
 open import Data.Fin
 open import Data.Product
 open import Data.Bool
 open Var

 data Expr : Arity → Set where
    var    : (v : Var) → Expr (Var.a v) 
    const  : {α : Arity} → Val α → Expr α
    -- TODO def-const
    _′_    : {α β : Arity} → Expr (α ↠ β) → Expr α → Expr β
    <_>_ : {β : Arity} → (v : Var) → Expr β → Expr (Var.a v ↠ β) 
    _,_    : {α : Arity} {n : ℕ} {as : Vec Arity n} →
               Expr α → Expr [[ as ]] → Expr [[ α ∷ as ]]
    [_]•_  : {α : Arity} →
               Expr α → (k : Fin (length α)) → Expr (nth α k)
 infixr 10 _,_
 infixl 12 <_>_

 open import Data.List

 free-variables : {β : Arity} → Expr β → List (String × Arity)
 free-variables (var (x ∈ α)) = (x , α) ∷ []
 free-variables (const x)   = []
 free-variables (a↠b ′ a)   = free-variables a↠b Data.List.++ free-variables a
 free-variables (< x > e) = dropWhile (λ v → proj₁ v == Var.l x) (free-variables e)
 free-variables (a , as)    = free-variables a Data.List.++ free-variables as
 free-variables ([ e ]• k)  = free-variables e
 -- TODO think duplication?
 fv = free-variables

 postulate
  change : {α : Arity} → String → Expr α → String

 open import Data.Nat
 _is-in_as-free-var : {β : Arity} → Var → Expr β → Bool
 x is-in e as-free-var = {!!} --Data.List.length (takeWhile (λ v → proj₁ v == x) (fv e)))
 
 replace : {α : Arity} → Expr α → String → String → Expr α
 replace (var (x ∈ α)) old new with x == old
 ... | true  = var (new ∈ α)
 ... | false = var (x ∈ α)
 replace (const x) old new = const x
 replace (a↠b ′ a) old new = replace a↠b old new ′ replace a old new
 replace (< x > e) old new with Var.l x == old
 ... | true  = {!!} --< new > replace e old new
 ... | false = < x > replace e old new
 replace (a , as) old new = replace a old new , replace as old new
 replace ([ a ]• i) old new = [ replace a old new ]• i

 α-conv : {α : Arity} → Expr α → String → Expr α
 α-conv (< x ∈ α > e) new = replace (< x ∈ α > e) x new
 α-conv other _ = other

 assign' : {β : Arity} → Expr β → 
             List (String × Arity) → (v : Var) → Expr (Var.a v) → Expr β
 assign' (var (x ∈ a)) [] v e with (x ∈ a) =v v
 ... | true = {!!} -- e? but arity is different
 ... | false = var (x ∈ a)
 assign' (const x) [] v e  = const x
 assign' (a↠b ′ a) [] v e  = {!!} -- a↠b ′ (assign' a (fv e) v e)
 assign' (< x > b) [] v e with {!!}
 ... | true  = < x > b
 ... | false with x is-in e as-free-var
 ... | true = {!!} --assign' (α-conv (< x > b) ?) [] v e -- maybe not terminated
 ... | false = < x > assign' b [] v e
 assign' (a , as)  [] v e   = assign' a [] v e , assign' as [] v e
 assign' ([ a ]• i) [] v e  = [ assign' a [] v e ]• i
 assign' b (x ∷ xs) v e     = {!!} --TBD

 -- substitution
 _[_≔_] : {β : Arity} → Expr β → (v : Var) → Expr (Var.a v) → Expr β
 _[_≔_] {β} b v e = assign' b [] v e

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

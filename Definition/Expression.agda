module Definition.Expression where

open import Definition.Arity
open import Definition.Variable
open import Definition.Constant

open import Data.Nat using (ℕ)

open import Data.Vec hiding ([_])
open import Data.Fin


data Expr : Arity → Set where
   var    : {α : Arity} → Var α   → Expr α 
   const  : {α : Arity} → Const α → Expr α
   -- TODO def-const
   app    : {α β : Arity} → Expr (α ↠ β) → Expr α → Expr β
   <_>_ : {α β : Arity} → Var α → Expr β → Expr (α ↠ β) 
   _,_    : {α : Arity} {n : ℕ} {as : Vec Arity n} →
              Expr α → Expr [[ as ]] → Expr [[ α ∷ as ]]
   [_]̇∙_  : {α : Arity} →
              Expr α → (k : Fin (length α)) → Expr (nth α k)
infixr 10 _,_
infixl 12 <_>_
{-
open import Data.List renaming (_++_ to _L++_)
free-variables : {β : Arity} → Expr β → List Var
free-variables (var (x ∈ α)) = (x ∈ α) ∷ []
free-variables (const x)   = []
free-variables (a↠b ′ a)   = free-variables a↠b L++ free-variables a
free-variables (< x > e)   = dropWhile (λ v → Var.l v == Var.l x) (free-variables e)
free-variables (a , as)    = free-variables a L++ free-variables as
free-variables ([ e ]• k)  = free-variables e
-- TODO think duplication?
fv = free-variables

open import Data.Nat
_is-in_as-free-var : {β : Arity} → Var → Expr β → Bool
x is-in e as-free-var = any (λ v → Var.l v == Var.l x) (fv e)

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

α-conv : {α : Arity} → Expr α → Expr α
α-conv (< x ∈ α > e) = {!!} --replace (< x ∈ α > e) x new TODO
α-conv other = other

-}
-- substitution
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary

infix 5 _[_≔_]

_[_≔_] : {α β : Arity} → Expr β → (v : Var α) → Expr α → Expr β
b [ x ≔ a ] = {!!}

infix 5 _≡_∈_
data _≡_∈_ : {α : Arity} → Expr α → Expr α → Arity → Set where
  var-eq   : {α : Arity} {x : Var α}   → var x   ≡ var x   ∈ α
  const-eq : {α : Arity} {c : Const α} → const c ≡ const c ∈ α
  -- 3. definiendum ≡ definiens
  apply-eq : {α β : Arity} {a a' : Expr (α ↠ β)} {b b' : Expr α} →
               a ≡ a' ∈ (α ↠ β) → b ≡ b' ∈ α →
               (app a b) ≡ (app a' b') ∈ β
  β-rule   : {α β : Arity} {b : Expr β} {a : Expr α} {x : Var α} → 
               app (< x > b) a ≡ b [ x ≔ a ] ∈ β 
  ξ-rule   : {α β : Arity} {b b' : Expr β} {x : Var α} →
              b ≡ b' ∈ β → < x > b ≡ < x > b' ∈ α ↠ β
  -- α-rule




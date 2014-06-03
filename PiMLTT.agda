module PiMLTT where

-- a formalization of "Programming in Martin-Lof's Type Theory"(PiMLTT)

-- Chapter 3 Expressions and definitional equality

-- 3.1 Application

data Expr : Set where

_(_) : Expr → Expr → Expr

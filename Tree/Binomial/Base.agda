{-# OPTIONS --without-K --safe #-}

module Tree.Binomial.Base where

open import Level using (Level)
open import Relation.Unary
open import Data.Nat.Base
open import DVec

private
  variable
    a : Level
    A : Set a

data Tree (A : Set a) : ℕ → Set a where
  conj : ∀ {n} → A → DVec (Tree A) n → Tree A n

link : ∀ {n} → Tree A n → Tree A n → Tree A (suc n)
link t (conj x ts) = conj x (t ∷ ts)

root : ∀ {n} → Tree A n → A
root (conj x ts) = x

rank0 : A → Tree A 0
rank0 x = conj x []

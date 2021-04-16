{-# OPTIONS --without-K --safe #-}

module DVec where

open import Level using (Level; _⊔_)
open import Relation.Unary
open import Data.Nat.Base hiding (_⊔_)

private
  variable
    a p : Level

infixr 5 _∷_

data DVec (A : Pred ℕ a) : ℕ → Set a where
  [] : DVec A zero
  _∷_ : ∀ {n} (x : A n) (xs : DVec A n) → DVec A (suc n)

data All {A : Pred ℕ a} (P : ∀ {n} → Pred (A n) p) : ∀ {n} → DVec A n → Set (p ⊔ a) where
  [] : All P []
  _∷_ : ∀ {n} {x} {xs : DVec A n} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles

module Tree.Binomial.Heap
  {a b ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂)
  (A : Set b) (key : A → TotalOrder.Carrier totalOrder) where

open TotalOrder totalOrder renaming (Carrier to K)

open import Level
open import Data.Product

open import DVec
open import Tree.Binomial.Base

infix 9 _#_
data _#_ (k : K) : ∀ {n} → Tree A n → Set (a ⊔ b ⊔ ℓ₂) where
  #-conj : ∀ {n x} {ts : DVec (Tree A) n} → k ≤ key x → k # conj x ts

data Heap : ∀ {n} → Tree A n → Set (a ⊔ b ⊔ ℓ₂) where
  heap : ∀ {n x} {ts : DVec (Tree A) n} → All (λ _ t → key x # t × Heap t) ts → Heap (conj x ts)

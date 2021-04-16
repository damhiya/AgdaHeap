{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles
  
module Tree.Binomial.PriorityQueue
  {a b ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂)
  (A : Set b) (key : A → TotalOrder.Carrier totalOrder) where

open TotalOrder totalOrder renaming (Carrier to K)
  
open import Level
open import Function.Base
open import Data.Product
open import Data.Maybe.Base
open import Data.Nat.Base using (_<_)
open import Data.List.Base as List
open import Data.List.Relation.Unary.Linked
open import Data.List.Extrema totalOrder

open import DVec
open import Tree.Binomial.Base
open import Tree.Binomial.Heap totalOrder A key
  
record PQueue : Set (a ⊔ b ⊔ ℓ₂) where
  field
    forest : List (∃[ n ] Σ[ h ∈ Tree A n ] Heap h)
    forest-↗ : Linked (_<_ on proj₁) forest

open PQueue
  
empty : PQueue
empty = record
  { forest = []
  ; forest-↗ = []
  }

singleton : A → PQueue
singleton x = record
  { forest = [ 0 , rank0 x , heap [] ]
  ; forest-↗ = [-]
  }

findMin : PQueue → Maybe A
findMin h with List.map (root ∘ proj₁ ∘ proj₂) (forest h)
... | [] = nothing
... | x ∷ xs = just (argmax key x xs)

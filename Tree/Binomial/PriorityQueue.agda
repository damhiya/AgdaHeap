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
open import Data.List.Relation.Unary.All
open import Data.List.Extrema totalOrder

open import DVec hiding (All)
open import Tree.Binomial.Base
open import Tree.Binomial.Heap totalOrder A key

record PQueue : Set (a ⊔ b ⊔ ℓ₂) where
  field
    forest : List (∃[ n ] Tree A n )
    forest-↗ : Linked (_<_ on proj₁) forest
    forest-heap : All (Heap ∘ proj₂) forest

open PQueue

empty : PQueue
empty = record
  { forest = []
  ; forest-↗ = []
  ; forest-heap = []
  }

singleton : A → PQueue
singleton x = record
  { forest = [ 0 , rank0 x ]
  ; forest-↗ = [-]
  ; forest-heap = heap [] ∷ []
  }

findMin : PQueue → Maybe A
findMin q with List.map (root ∘ proj₂) (forest q)
... | [] = nothing
... | x ∷ xs = just (argmin key x xs)

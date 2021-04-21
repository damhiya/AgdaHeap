open import Relation.Binary.Bundles

module Tree.WBLT.PriorityQueue
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

open import Level
open import Data.Product
open import Data.Bool
open import Data.Maybe.Base
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality.Core
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ

open TotalOrder totalOrder renaming (Carrier to K) hiding (refl)
open import Tree.WBLT.Base totalOrder renaming (size to #node; null to null?)

private
  variable
    b : Level

module _ (A : Set b) (key : A → K) where
  record WBLT : Set (b ⊔ ℓ₂) where
    field
      tree : Tree A key
      @0 leftist : Leftist {key = key} tree
      @0 heap : Heap {key = key} tree

open WBLT

module PQueue {A : Set b} {key : A → K} where
  meld : WBLT A key → WBLT A key → WBLT A key
  meld wblt₁ wblt₂ = record
    { tree = merge {key = key} (tree wblt₁) (tree wblt₂)
    ; leftist = merge-leftist {key = key} (leftist wblt₁) (leftist wblt₂)
    ; heap = merge-heap {key = key} (heap wblt₁) (heap wblt₂)
    }

  size : WBLT A key → ℕ
  size wblt = #node {key = key} (tree wblt)

  null : WBLT A key → Bool
  null wblt = null? {key = key} (tree wblt)

  empty : WBLT A key
  empty = record
    { tree = nil
    ; leftist = leftist-nil
    ; heap = heap-nil
    }

  singleton : A → WBLT A key
  singleton x = record
    { tree = node x 1 nil nil
    ; leftist = leftist-node refl ℕ.z≤n leftist-nil leftist-nil
    ; heap = heap-node #-nil #-nil heap-nil heap-nil
    }

  insert : A → WBLT A key → WBLT A key
  insert x wblt = meld wblt (singleton x)

  findMin : WBLT A key → Maybe A
  findMin wblt = root {key = key} (tree wblt)

  deleteMin : WBLT A key → Maybe (WBLT A key)
  deleteMin record {tree = nil} = nothing
  deleteMin record
    { tree = node x _ tₗ tᵣ
    ; leftist = leftist-node _ _ lₗ lᵣ
    ; heap = heap-node _ _ hₗ hᵣ
    } = just record
      { tree = merge tₗ tᵣ
      ; leftist = merge-leftist lₗ lᵣ
      ; heap = merge-heap hₗ hᵣ
      }

  popMin : WBLT A key → Maybe (A × WBLT A key)
  popMin record {tree = nil} = nothing
  popMin record
    { tree = node x _ tₗ tᵣ
    ; leftist = leftist-node _ _ lₗ lᵣ
    ; heap = heap-node _ _ hₗ hᵣ
    } = just (x , record
      { tree = merge tₗ tᵣ
      ; leftist = merge-leftist lₗ lᵣ
      ; heap = merge-heap hₗ hᵣ
      })

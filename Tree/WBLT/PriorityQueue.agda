{-# OPTIONS --with-K --safe #-}

open import Relation.Binary.Bundles

module Tree.WBLT.PriorityQueue
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

open import Level hiding (suc)
open import Function.Base
open import Data.Product
open import Data.Bool hiding (_≤_)
open import Data.Maybe.Base as Maybe
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.List.Base using (List; unfold)
open import Data.List.Relation.Unary.Linked
open import Relation.Binary.PropositionalEquality.Core
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ

open TotalOrder totalOrder renaming (Carrier to K) hiding (refl)
import Tree.WBLT.Base totalOrder as Tree
open Tree using
  ( Tree; nil; node
  ; Leftist; leftist-nil; leftist-node
  ; #-nil; #-node
  ; Heap; heap-nil; heap-node
  ; merge; merge-leftist; merge-heap
  )

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
  size wblt = Tree.size {key = key} (tree wblt)

  null : WBLT A key → Bool
  null wblt = Tree.null {key = key} (tree wblt)

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

  findMin : WBLT A key → Maybe A
  findMin wblt = Tree.findMin {key = key} (tree wblt)

  deleteMin : WBLT A key → Maybe (WBLT A key)
  deleteMin = Maybe.map proj₂ ∘ popMin

  toList : WBLT A key → List A
  toList wblt = Tree.toList {key = key} (tree wblt)

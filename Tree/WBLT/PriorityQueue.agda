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

open TotalOrder totalOrder renaming (Carrier to A) hiding (refl)
import Tree.WBLT.Base totalOrder as Tree
open Tree using
  ( Tree; nil; node
  ; Leftist; leftist-nil; leftist-node
  ; #-nil; #-node
  ; Heap; heap-nil; heap-node
  ; merge; merge-leftist; merge-heap
  )

record WBLT : Set (a ⊔ ℓ₂) where
  field
    tree : Tree
    @0 leftist : Leftist tree
    @0 heap : Heap tree

open WBLT

meld : WBLT → WBLT → WBLT
meld wblt₁ wblt₂ = record
  { tree = merge (tree wblt₁) (tree wblt₂)
  ; leftist = merge-leftist (leftist wblt₁) (leftist wblt₂)
  ; heap = merge-heap (heap wblt₁) (heap wblt₂)
  }

size : WBLT → ℕ
size wblt = Tree.size (tree wblt)

null : WBLT → Bool
null wblt = Tree.null (tree wblt)

empty : WBLT
empty = record
  { tree = nil
  ; leftist = leftist-nil
  ; heap = heap-nil
  }

singleton : A → WBLT
singleton x = record
  { tree = node x 1 nil nil
  ; leftist = leftist-node refl ℕ.z≤n leftist-nil leftist-nil
  ; heap = heap-node #-nil #-nil heap-nil heap-nil
  }

insert : A → WBLT → WBLT
insert x wblt = meld wblt (singleton x)

popMin : WBLT → Maybe (A × WBLT)
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

findMin : WBLT → Maybe A
findMin wblt = Tree.findMin (tree wblt)

deleteMin : WBLT → Maybe WBLT
deleteMin = Maybe.map proj₂ ∘ popMin

toList : WBLT → List A
toList wblt = Tree.toList (tree wblt)

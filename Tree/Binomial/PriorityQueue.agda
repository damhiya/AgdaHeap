{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles

module Tree.Binomial.PriorityQueue
  {a b ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂)
  (A : Set b) (key : A → TotalOrder.Carrier totalOrder) where

open TotalOrder totalOrder renaming (Carrier to K)

open import Level using (Level; _⊔_)
open import Function.Base
open import Data.Product
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Maybe.Base
open import Data.Nat.Base using (suc; _<_)
open import Data.Nat.Properties
open import Data.List.Base as List
open import Data.List.Relation.Unary.Linked
open import Data.List.Relation.Unary.All
open import Data.List.Extrema totalOrder
open import Relation.Unary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core

open import DVec hiding (All)
open import Tree.Binomial.Base
open import Tree.Binomial.Heap totalOrder A key

Rank↗ : Pred (List (∃[ n ] Tree A n)) b
Rank↗ = Linked (_<_ on proj₁)

Heaps : Pred (List (∃[ n ] Tree A n)) (a ⊔ b ⊔ ℓ₂)
Heaps = All (Heap ∘ proj₂)

record PQueue : Set (a ⊔ b ⊔ ℓ₂) where
  field
    forest : List (∃[ n ] Tree A n )
    forest-↗ : Rank↗ forest
    forest-heap : Heaps forest

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

private
  link′ : ∀ {n} → Tree A n → Tree A n → Tree A (suc n)
  link′ h₁@(conj x xs) h₂@(conj y ys) with total (key x) (key y)
  ... | inj₁ kx≤ky = link h₂ h₁
  ... | inj₂ ky≤kx = link h₁ h₂

  link′-heap : ∀ {n} {h₁ h₂ : Tree A n} → Heap h₁ → Heap h₂ → Heap (link′ h₁ h₂)
  link′-heap {h₁ = conj x xs} {h₂ = conj y ys} (heap hs₁) (heap hs₂) with total (key x) (key y)
  ... | inj₁ kx≤ky = heap ((#-conj kx≤ky , heap hs₂) ∷ hs₁)
  ... | inj₂ ky≤kx = heap ((#-conj ky≤kx , heap hs₁) ∷ hs₂)

  increment : ∀ {m} → Tree A m → List (∃[ n ] Tree A n) → List (∃[ n ] Tree A n)
  increment x [] = [ -, x ]
  increment {m = m} x ((n , y) ∷ ys) with <-cmp m n
  ... | tri< _ _ _ = (-, x) ∷ (-, y) ∷ ys
  ... | tri≈ _ refl _ = increment (link x y) ys
  ... | tri> _ _ _ = (-, y) ∷ increment x ys

  open import Data.Nat.Properties

  increment-↗ : ∀ m (x : Tree A m) ys → Rank↗ ys → Rank↗ (increment x ys)
  increment-↗ m x [] _ = {!!}
  increment-↗ m x ((n₁ , y₁) ∷ []) _ = {!!}
  increment-↗ m x ((n₁ , y₁) ∷ (n₂ , y₂) ∷ y) _ = {!!}
  -- increment-↗ {x = x} {ys = []} _ = [-]
  -- increment-↗ {m = m} {x = x} {ys = (n , y) ∷ ys} _ with <-cmp m n
  -- increment-↗ rank↗ | tri< m<n _ _ = m<n ∷ rank↗
  -- increment-↗ [-] | tri≈ _ refl _ = [-]
  -- increment-↗ {x = x} {ys = (_ , y) ∷ _} (n<* ∷ rank↗) | tri≈ _ refl _ = increment-↗ {x = link x y} rank↗
  -- increment-↗ {ys = (n₁ , y₁) ∷ []} [-] | tri> _ _ n<m = n<m ∷ [-]
  -- increment-↗ {m = m} {x = x} {ys = (n₁ , y₁) ∷ (n₂ , y₂) ∷ ys} (n₁<n₂ ∷ rank↗) | tri> _ _ n₁<m with <-cmp m n₂
  -- ... | tri< m<n₂ _ _ = n₁<m ∷ m<n₂ ∷ rank↗
  -- ... | tri≈ _ refl _ = {!n<1+n n₁ ∷ increment-↗ _!}
  -- ... | tri> _ _ _ = {!!}

  increment-heap : ∀ {m} {x : Tree A m} {xs} → Heap x → Heaps xs → Heaps (increment x xs)
  increment-heap = {!!}

insert : A → PQueue → PQueue
insert x q = record
  { forest = increment (rank0 x) (forest q)
  ; forest-↗ = increment-↗ _ _ _ (forest-↗ q)
  ; forest-heap = {!!}
  }

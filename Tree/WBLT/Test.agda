open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.List.Base
open import Relation.Binary.PropositionalEquality.Core
open import Tree.WBLT.PriorityQueue ≤-totalOrder

module Tree.WBLT.Test where

xs : List ℕ
xs = 1 ∷ 4 ∷ 2 ∷ 8 ∷ 5 ∷ 7 ∷ 4 ∷ 8 ∷ []

xs-heap : WBLT
xs-heap = foldr (λ x h → meld h (singleton x)) empty xs

xs-sorted : List ℕ
xs-sorted = toList xs-heap

xs-sorted-is : xs-sorted ≡ 1 ∷ 2 ∷ 4 ∷ 4 ∷ 5 ∷ 7 ∷ 8 ∷ 8 ∷ []
xs-sorted-is = refl

{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_; 0ℓ)
open import Function.Base
open import Data.Product
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base
open import Data.Maybe.Base as Maybe
open import Data.Bool hiding (_≤_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.List.Base hiding (null; merge)
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.Core
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality.Core
open import Induction.WellFounded

import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
import Data.Tree.Binary as Binary

module Tree.WBLT.Base {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

open TotalOrder totalOrder renaming (Carrier to A) hiding (refl)

Tree : Set a
Tree = Binary.Tree (A × ℕ) ⊤

pattern nil = Binary.leaf tt
pattern node x n l r = Binary.node l (x , n) r

count : Tree → ℕ
count nil = 0
count (node _ _ tₗ tᵣ) = suc (count tₗ + count tᵣ)

size : Tree → ℕ
size nil = 0
size (node _ n _ _) = n

null : Tree → Bool
null nil = true
null (node _ _ _ _) = false

data Leftist : Tree → Set a where
  leftist-nil : Leftist nil
  leftist-node : ∀ {x n tₗ tᵣ} →
                   n ≡ suc (count tₗ + count tᵣ) →
                   count tₗ ℕ.≥ count tᵣ →
                   Leftist tₗ →
                   Leftist tᵣ →
                   Leftist (node x n tₗ tᵣ)

data _#_ (k : A) : Tree → Set (a ⊔ ℓ₂) where
  #-nil : k # nil
  #-node : ∀ {x n tₗ tᵣ} → k ≤ x → k # node x n tₗ tᵣ

data Heap : Tree → Set (a ⊔ ℓ₂) where
  heap-nil : Heap nil
  heap-node : ∀ {x n tₗ tᵣ} →
              x # tₗ →
              x # tᵣ →
              Heap tₗ →
              Heap tᵣ →
              Heap (node x n tₗ tᵣ)

Leftist⇒size≡count : ∀ {t : Tree} → Leftist t → size t ≡ count t
Leftist⇒size≡count leftist-nil = refl
Leftist⇒size≡count (leftist-node size≡count _ _ _) = size≡count

data ¬Null (x : A) : Tree → Set a where
  ¬null : ∀ {n tₗ tᵣ} → ¬Null x (node x n tₗ tᵣ)

merge : Tree → Tree → Tree
merge nil nil = nil
merge nil t@(node _ _ _ _) = t
merge t@(node _ _ _ _) nil = t
merge t₁@(node x₁ n₁ tₗ₁ tᵣ₁) t₂@(node x₂ n₂ tₗ₂ tᵣ₂) =
  [ const (aux x₁ tₗ₁ (merge tᵣ₁ t₂))
  , const (aux x₂ tₗ₂ (merge t₁ tᵣ₂))
  ]′ (total x₁ x₂)
  where
    aux : A → Tree → Tree → Tree
    aux x t₁ t₂ with ℕ.≤-total (size t₂) (size t₁)
    ... | inj₁ _ = node x (suc (size t₁ + size t₂)) t₁ t₂
    ... | inj₂ _ = node x (suc (size t₂ + size t₁)) t₂ t₁

open ≡-Reasoning
private
  open import Data.Nat.Tactic.RingSolver

  nat-lemma₁ : ∀ x y z w → w ≡ y + z → suc (x + w) ≡ suc ((x + y) + z)
  nat-lemma₁ x y z w p = begin
    suc (x + w)       ≡⟨ cong (suc ∘ (x +_)) p ⟩
    suc (x + (y + z)) ≡⟨ solve (x ∷ y ∷ z ∷ []) ⟩
    suc ((x + y) + z) ∎

  nat-lemma₂ : ∀ x y z w → w ≡ x + y → suc (w + z) ≡ suc ((z + x) + y)
  nat-lemma₂ x y z w p = begin
    suc (w + z)       ≡⟨ cong (suc ∘ (_+ z)) p ⟩
    suc ((x + y) + z) ≡⟨ solve (x ∷ y ∷ z ∷ []) ⟩
    suc ((z + x) + y) ∎

  nat-lemma₃ : ∀ x y z w → w ≡ y + z → suc (x + w) ≡ y + suc (x + z)
  nat-lemma₃ x y z w p = begin
    suc (x + w)       ≡⟨ cong (suc ∘ (x +_)) p ⟩
    suc (x + (y + z)) ≡⟨ solve (x ∷ y ∷ z ∷ []) ⟩
    y + suc (x + z)   ∎

  nat-lemma₄ : ∀ x y z w → w ≡ x + y → suc (w + z) ≡ x + suc (z + y)
  nat-lemma₄ x y z w p = begin
    suc (w + z)       ≡⟨ cong (suc ∘ (_+ z)) p ⟩
    suc ((x + y) + z) ≡⟨ solve (x ∷ y ∷ z ∷ []) ⟩
    x + suc (z + y)   ∎

merge-count : ∀ (t₁ t₂ : Tree) → count (merge t₁ t₂) ≡ count t₁ + count t₂
merge-count nil nil = refl
merge-count nil t@(node _ _ _ _) = refl
merge-count t@(node _ _ _ _) nil = sym (ℕ.+-identityʳ (count t))
merge-count t₁@(node x₁ n₁ tₗ₁ tᵣ₁) t₂@(node x₂ n₂ tₗ₂ tᵣ₂)
  = aux (merge-count tᵣ₁ t₂) (merge-count t₁ tᵣ₂)
  where
    aux : count (merge tᵣ₁ t₂ ) ≡ count tᵣ₁ + count t₂ →
          count (merge t₁  tᵣ₂) ≡ count t₁  + count tᵣ₂ →
          count (merge t₁  t₂ ) ≡ count t₁  + count t₂
    aux with total x₁ x₂
    aux | inj₁ _ with ℕ.≤-total (size (merge tᵣ₁ t₂)) (size tₗ₁)
    ...          | inj₁ _ = λ p _ → nat-lemma₁ (count tₗ₁) (count tᵣ₁) (count t₂) _ p
    ...          | inj₂ _ = λ p _ → nat-lemma₂ (count tᵣ₁) (count t₂) (count tₗ₁) _ p
    aux | inj₂ _ with ℕ.≤-total (size (merge t₁ tᵣ₂)) (size tₗ₂)
    ...          | inj₁ _ = λ _ p → nat-lemma₃ (count tₗ₂) (count t₁) (count tᵣ₂) _ p
    ...          | inj₂ _ = λ _ p → nat-lemma₄ (count t₁) (count tᵣ₂) (count tₗ₂) _ p

merge-leftist : ∀ {t₁ t₂ : Tree} → Leftist t₁ → Leftist t₂ → Leftist (merge t₁ t₂)
merge-leftist leftist-nil leftist-nil = leftist-nil
merge-leftist leftist-nil l₂@(leftist-node _ _ _ _) = l₂
merge-leftist l₁@(leftist-node _ _ _ _) leftist-nil = l₁
merge-leftist {t₁ = t₁@(node x₁ n₁ tₗ₁ tᵣ₁)} {t₂ = t₂@(node x₂ n₂ tₗ₂ tᵣ₂)}
               l₁@(leftist-node _ _ lₗ₁ lᵣ₁)  l₂@(leftist-node _ _ lₗ₂ lᵣ₂)
  = aux (merge-leftist lᵣ₁ l₂) (merge-leftist l₁ lᵣ₂)
  where
    aux : Leftist (merge tᵣ₁ t₂) → Leftist (merge t₁ tᵣ₂) → Leftist (merge t₁ t₂)
    aux with total x₁ x₂
    aux | inj₁ _ with ℕ.≤-total (size (merge tᵣ₁ t₂)) (size tₗ₁)
    ... | inj₁ [tₗ₁]≥[tᵣ′] = λ lᵣ′ _ → leftist-node
          (cong₂ (suc ∘₂ _+_) (Leftist⇒size≡count lₗ₁) (Leftist⇒size≡count lᵣ′))
          (subst₂ ℕ._≥_       (Leftist⇒size≡count lₗ₁) (Leftist⇒size≡count lᵣ′) [tₗ₁]≥[tᵣ′])
          lₗ₁ lᵣ′
    ... | inj₂ [tᵣ′]≥[tₗ₁] = λ lᵣ′ _ → leftist-node
          (cong₂ (suc ∘₂ _+_) (Leftist⇒size≡count lᵣ′) (Leftist⇒size≡count lₗ₁))
          (subst₂ ℕ._≥_       (Leftist⇒size≡count lᵣ′) (Leftist⇒size≡count lₗ₁) [tᵣ′]≥[tₗ₁])
          lᵣ′ lₗ₁
    aux | inj₂ _ with ℕ.≤-total (size (merge t₁ tᵣ₂)) (size tₗ₂)
    ... | inj₁ [tₗ₂]≥[tᵣ′] = λ _ lᵣ′ → leftist-node
          (cong₂ (suc ∘₂ _+_) (Leftist⇒size≡count lₗ₂) (Leftist⇒size≡count lᵣ′))
          (subst₂ ℕ._≥_       (Leftist⇒size≡count lₗ₂) (Leftist⇒size≡count lᵣ′) [tₗ₂]≥[tᵣ′])
          lₗ₂ lᵣ′
    ... | inj₂ [tᵣ′]≥[tₗ₂] = λ _ lᵣ′ → leftist-node
          (cong₂ (suc ∘₂ _+_) (Leftist⇒size≡count lᵣ′) (Leftist⇒size≡count lₗ₂))
          (subst₂ ℕ._≥_       (Leftist⇒size≡count lᵣ′) (Leftist⇒size≡count lₗ₂) [tᵣ′]≥[tₗ₂])
          lᵣ′ lₗ₂

merge-size : ∀ {t₁ t₂ : Tree} → Leftist t₁ → Leftist t₂ → size (merge t₁ t₂) ≡ size t₁ + size t₂
merge-size {t₁ = t₁} {t₂ = t₂} l₁ l₂ = begin
  size (merge t₁ t₂)  ≡⟨ Leftist⇒size≡count (merge-leftist l₁ l₂) ⟩
  count (merge t₁ t₂) ≡⟨ merge-count t₁ t₂ ⟩
  count t₁ + count t₂ ≡˘⟨ cong₂ _+_ (Leftist⇒size≡count l₁) (Leftist⇒size≡count l₂) ⟩
  size t₁ + size t₂ ∎

merge-# : ∀ {x : A} {t₁ t₂ : Tree} → x # t₁ → x # t₂ → x # merge t₁ t₂
merge-# #-nil #-nil = #-nil
merge-# #-nil x#t₂@(#-node _) = x#t₂
merge-# x#t₁@(#-node _) #-nil = x#t₁
merge-# {x = x} {t₁ = t₁@(node x₁ n₁ tₗ₁ tᵣ₁)} {t₂ = t₂@(node x₂ n₂ tₗ₂ tᵣ₂)}
                (#-node x≤x₁)                  (#-node x≤x₂)
  = aux
  where
    aux : x # merge t₁ t₂
    aux with total x₁ x₂
    aux | inj₁ _ with ℕ.≤-total (size (merge tᵣ₁ t₂)) (size tₗ₁)
    ... | inj₁ _ = #-node x≤x₁
    ... | inj₂ _ = #-node x≤x₁
    aux | inj₂ _ with ℕ.≤-total (size (merge t₁ tᵣ₂)) (size tₗ₂)
    ... | inj₁ _ = #-node x≤x₂
    ... | inj₂ _ = #-node x≤x₂

merge-heap : ∀ {t₁ t₂ : Tree} → Heap t₁ → Heap t₂ → Heap (merge t₁ t₂)
merge-heap heap-nil heap-nil = heap-nil
merge-heap heap-nil h₂@(heap-node _ _ _ _) = h₂
merge-heap h₁@(heap-node _ _ _ _) heap-nil = h₁
merge-heap {t₁ = t₁@(node x₁ n₁ tₗ₁ tᵣ₁)}       {t₂ = t₂@(node x₂ n₂ tₗ₂ tᵣ₂)}
                 h₁@(heap-node x₁#tₗ₁ x₁#tᵣ₁ hₗ₁ hᵣ₁) h₂@(heap-node x₂#tₗ₂ x₂#tᵣ₂ hₗ₂ hᵣ₂)
  = aux (merge-heap hᵣ₁ h₂) (merge-heap h₁ hᵣ₂)
  where
    aux : Heap (merge tᵣ₁ t₂) → Heap (merge t₁ tᵣ₂) → Heap (merge t₁ t₂)
    aux with total x₁ x₂
    aux | inj₁ x₁≤x₂ with ℕ.≤-total (size (merge tᵣ₁ t₂)) (size tₗ₁)
    ... | inj₁ _ = λ hᵣ′ _ → heap-node x₁#tₗ₁ (merge-# x₁#tᵣ₁ (#-node x₁≤x₂)) hₗ₁ hᵣ′
    ... | inj₂ _ = λ hᵣ′ _ → heap-node (merge-# x₁#tᵣ₁ (#-node x₁≤x₂)) x₁#tₗ₁ hᵣ′ hₗ₁
    aux | inj₂ x₂≤x₁ with ℕ.≤-total (size (merge t₁ tᵣ₂)) (size tₗ₂)
    ... | inj₁ _ = λ _ hᵣ′ → heap-node x₂#tₗ₂ (merge-# (#-node x₂≤x₁) x₂#tᵣ₂) hₗ₂ hᵣ′
    ... | inj₂ _ = λ _ hᵣ′ → heap-node (merge-# (#-node x₂≤x₁) x₂#tᵣ₂) x₂#tₗ₂ hᵣ′ hₗ₂

merge-¬null : ∀ {x₁ x₂} (t₁ t₂ : Tree) → ¬Null x₁ t₁ → ¬Null x₂ t₂ → (¬Null x₁ ∪ ¬Null x₂) (merge t₁ t₂)
merge-¬null t₁@(node x₁ n₁ tₗ₁ tᵣ₁) t₂@(node x₂ n₂ tₗ₂ tᵣ₂) ¬null ¬null = aux
  where
    aux : (¬Null x₁ ∪ ¬Null x₂) (merge t₁ t₂)
    aux with total x₁ x₂
    aux | inj₁ _ with ℕ.≤-total (size (merge tᵣ₁ t₂)) (size tₗ₁)
    ... | inj₁ _ = inj₁ ¬null
    ... | inj₂ _ = inj₁ ¬null
    aux | inj₂ _ with ℕ.≤-total (size (merge t₁ tᵣ₂)) (size tₗ₂)
    ... | inj₁ _ = inj₂ ¬null
    ... | inj₂ _ = inj₂ ¬null

popMin : Tree → Maybe (A × Tree)
popMin nil = nothing
popMin (node x _ tₗ tᵣ) = just (x , merge tₗ tᵣ)

findMin : Tree → Maybe A
findMin = Maybe.map proj₁ ∘ popMin

deleteMin : Tree → Maybe Tree
deleteMin = Maybe.map proj₂ ∘ popMin

data DeleteMin : Rel Tree a where
  delmin : ∀ {x n tₗ tᵣ} → DeleteMin (merge tₗ tᵣ) (node x n tₗ tᵣ)

DeleteMin⇒suc-on-count : ∀ {t₁ t₂} → DeleteMin t₁ t₂ → suc (count t₁) ≡ count t₂
DeleteMin⇒suc-on-count (delmin {tₗ = tₗ} {tᵣ = tᵣ}) = cong suc (merge-count tₗ tᵣ)

count⇒Acc-DeleteMin : ∀ {n} (t : Tree) → count t ≡ n → Acc DeleteMin t
count⇒Acc-DeleteMin nil _ = acc λ _ ()
count⇒Acc-DeleteMin {n = suc n} t@(node _ _ _ _) refl = acc λ t' t'<t →
  count⇒Acc-DeleteMin {n = n} t' (ℕ.suc-injective (DeleteMin⇒suc-on-count t'<t))

DeleteMin-wellFounded : WellFounded DeleteMin
DeleteMin-wellFounded t = count⇒Acc-DeleteMin t refl

toList′ : ∀ (t : Tree) → (@0 rec : Acc DeleteMin t) → List A
toList′ nil _ = []
toList′ t@(node x _ tₗ tᵣ) (acc rs) = x ∷ toList′ (merge tₗ tᵣ) (rs _ delmin)

toList′-head : ∀ {x} {t : Tree} → ¬Null x t → (@0 rec : Acc DeleteMin t) → ∃[ xs ] toList′ t rec ≡ x ∷ xs
toList′-head ¬null (acc rs) = -, refl

open import Data.List.Relation.Unary.Linked

_[_]∷_ : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} {x y : A} {xs : List A} → R x y → ∃[ ys ] xs ≡ y ∷ ys → Linked R xs → Linked R (x ∷ xs)
Rxy [ _ , refl ]∷ Rxs = Rxy ∷ Rxs

toList′-sorted : ∀ {t : Tree} → Heap t → (@0 rec : Acc DeleteMin t) → Linked _≤_ (toList′ t rec)
toList′-sorted heap-nil _ = []
toList′-sorted (heap-node _ _ heap-nil heap-nil) (acc _) = [-]
toList′-sorted {t = node x _ nil t@(node y _ _ _)}
               (heap-node _ (#-node x≤y) heap-nil h@(heap-node _ _ _ _)) (acc rs)
  = x≤y [ toList′-head ¬null (rs t delmin) ]∷ toList′-sorted h (rs t delmin)
toList′-sorted {t = node x _ t@(node y _ _ _) nil}
               (heap-node (#-node x≤y) _ h@(heap-node _ _ _ _) heap-nil) (acc rs)
  = x≤y [ toList′-head ¬null (rs t delmin) ]∷ toList′-sorted h (rs t delmin)
toList′-sorted {t = node x _ t₁@(node y₁ n₁ tₗ₁ tᵣ₁) t₂@(node y₂ n₂ tₗ₂ tᵣ₂)}
               (heap-node (#-node x≤y₁) (#-node x≤y₂) h₁@(heap-node _ _ _ _) h₂@(heap-node _ _ _ _)) (acc rs)
               with merge-¬null t₁ t₂ ¬null ¬null
... | inj₁ nn = x≤y₁ [ toList′-head nn (rs (merge t₁ t₂) delmin) ]∷ toList′-sorted (merge-heap h₁ h₂) (rs _ delmin)
... | inj₂ nn = x≤y₂ [ toList′-head nn (rs (merge t₁ t₂) delmin) ]∷ toList′-sorted (merge-heap h₁ h₂) (rs _ delmin)

toList : Tree → List A
toList t = toList′ t (DeleteMin-wellFounded _)

toList-sorted : ∀ {t : Tree} → Heap t → Linked _≤_ (toList t)
toList-sorted h = toList′-sorted h (DeleteMin-wellFounded _)

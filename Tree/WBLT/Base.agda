open import Level using (Level; _⊔_; 0ℓ)
open import Data.Product
open import Data.Product.Relation.Binary.Lex.Strict
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base
open import Data.Maybe.Base
open import Data.Bool hiding (_≤_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality.Core
open import Induction.WellFounded

import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ

module Tree.WBLT.Base {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

open TotalOrder totalOrder renaming (Carrier to K) hiding (refl)

private
  variable
    b : Level

module _ (A : Set b) (key : A → K) where
  import Data.Tree.Binary as Binary

  Tree : Set b
  Tree = Binary.Tree (A × ℕ) ⊤

  pattern nil = Binary.leaf tt
  pattern node x n l r = Binary.node l (x , n) r

module _ {A : Set b} {key : A → K} where
  size : Tree A key → ℕ
  size nil = 0
  size (node _ n _ _) = n

  null : Tree A key → Bool
  null nil = true
  null (node _ _ _ _) = false

  root : Tree A key → Maybe A
  root nil = nothing
  root (node x _ _ _) = just x

  data Leftist : Tree A key → Set where
    leftist-nil : Leftist nil
    leftist-node : ∀ {x n tₗ tᵣ} →
                     n ≡ suc (size tₗ + size tᵣ) →
                     size tₗ ℕ.≥ size tᵣ →
                     Leftist tₗ →
                     Leftist tᵣ →
                     Leftist (node x n tₗ tᵣ)

  data _#_ (k : K) : Tree A key → Set ℓ₂ where
    #-nil : k # nil
    #-node : ∀ {x n tₗ tᵣ} → k ≤ key x → k # node x n tₗ tᵣ

  data Heap : Tree A key → Set ℓ₂ where
    heap-nil : Heap nil
    heap-node : ∀ {x n tₗ tᵣ} →
                key x # tₗ →
                key x # tᵣ →
                Heap tₗ →
                Heap tᵣ →
                Heap (node x n tₗ tᵣ)

  data _≺_ : Rel (Tree A key) 0ℓ where
    ≺-base : ∀ {x n tₗ tᵣ} → tᵣ ≺ node x n tₗ tᵣ
    ≺-ind : ∀ {x n t tₗ tᵣ} → t ≺ tᵣ → t ≺ node x n tₗ tᵣ

  ≺-wellFounded : WellFounded _≺_
  ≺-wellFounded′ : ∀ t → WfRec _≺_ (Acc _≺_) t
  ≺-wellFounded t = acc (≺-wellFounded′ t)
  ≺-wellFounded′ nil _ ()
  ≺-wellFounded′ (node x n tₗ tᵣ) tᵣ ≺-base = ≺-wellFounded tᵣ
  ≺-wellFounded′ (node x n tₗ tᵣ) t (≺-ind t≺tᵣ) = ≺-wellFounded′ tᵣ t t≺tᵣ

  _≺ₗₑₓ_ : Rel (Tree A key × Tree A key) b
  _≺ₗₑₓ_ = ×-Lex _≡_ _≺_ _≺_

  ≺ₗₑₓ-wellFounded : WellFounded _≺ₗₑₓ_
  ≺ₗₑₓ-wellFounded = ×-wellFounded ≺-wellFounded ≺-wellFounded

  merge′ : ∀ (t₁ t₂ : Tree A key) → (@0 rec : Acc _≺ₗₑₓ_ (t₁ , t₂)) → Tree A key
  merge′ nil nil _ = nil
  merge′ nil t@(node _ _ _ _) _ = t
  merge′ t@(node _ _ _ _) nil _ = t
  merge′ t₁@(node x₁ _ _ _) h₂@(node x₂ _ _ _) _ with total (key x₁) (key x₂)
  merge′ t₁@(node x₁ n₁ tₗ tᵣ) t₂ (acc rec) | inj₁ _ with merge′ tᵣ t₂ (rec (tᵣ , t₂) (inj₁ ≺-base))
  ... | tᵣ′ with ℕ.≤-total (size tᵣ′) (size tₗ)
  ... | inj₁ _ = node x₁ (suc (size tₗ + size tᵣ′)) tₗ tᵣ′
  ... | inj₂ _ = node x₁ (suc (size tᵣ′ + size tₗ)) tᵣ′ tₗ
  merge′ t₁ t₂@(node x₂ n₂ tₗ tᵣ) (acc rec) | inj₂ _ with merge′ t₁ tᵣ ((rec (t₁ , tᵣ) (inj₂ (refl , ≺-base))))
  ... | tᵣ′ with ℕ.≤-total (size tᵣ′) (size tₗ)
  ... | inj₁ _ = node x₂ (suc (size tₗ + size tᵣ′)) tₗ tᵣ′
  ... | inj₂ _ = node x₂ (suc (size tᵣ′ + size tₗ)) tᵣ′ tₗ

  merge′-leftist : ∀ {t₁ t₂ : Tree A key} → Leftist t₁ → Leftist t₂ → (@0 rec : Acc _≺ₗₑₓ_ (t₁ , t₂)) → Leftist (merge′ t₁ t₂ rec)
  merge′-leftist leftist-nil leftist-nil _ = leftist-nil
  merge′-leftist leftist-nil l₂@(leftist-node _ _ _ _) _ = l₂
  merge′-leftist l₁@(leftist-node _ _ _ _) leftist-nil _ = l₁
  merge′-leftist {t₁ = node x₁ _ _ _} {t₂ = node x₂ _ _ _} (leftist-node _ _ _ _) (leftist-node _ _ _ _) _ with total (key x₁) (key x₂)
  merge′-leftist
    {t₁ = t₁@(node x₁ n₁ tₗ tᵣ)} {t₂ = t₂}
    (leftist-node _ _ lₗ lᵣ) l₂ (acc rec)
    | inj₁ _ with merge′ tᵣ t₂ (rec (tᵣ , t₂) (inj₁ ≺-base)) | merge′-leftist lᵣ l₂ (rec (tᵣ , t₂) (inj₁ ≺-base))
  ... | tᵣ′ | lᵣ′ with ℕ.≤-total (size tᵣ′) (size tₗ)
  ... | inj₁ size[tₗ]≥size[tᵣ′] = leftist-node refl size[tₗ]≥size[tᵣ′] lₗ lᵣ′
  ... | inj₂ size[tᵣ′]≥size[tₗ] = leftist-node refl size[tᵣ′]≥size[tₗ] lᵣ′ lₗ
  merge′-leftist
    {t₁ = t₁} {t₂ = t₂@(node x₂ n₂ tₗ tᵣ)}
    l₁ (leftist-node _ _ lₗ lᵣ) (acc rec)
    | inj₂ _ with merge′ t₁ tᵣ (rec (t₁ , tᵣ) (inj₂ (refl , ≺-base))) | merge′-leftist l₁ lᵣ (rec (t₁ , tᵣ) (inj₂ (refl , ≺-base)))
  ... | tᵣ′ | lᵣ′ with ℕ.≤-total (size tᵣ′) (size tₗ)
  ... | inj₁ size[tₗ]≥size[tᵣ′] = leftist-node refl size[tₗ]≥size[tᵣ′] lₗ lᵣ′
  ... | inj₂ size[tᵣ′]≥size[tₗ] = leftist-node refl size[tᵣ′]≥size[tₗ] lᵣ′ lₗ

  merge′-# : ∀ {k : K} {t₁ t₂ : Tree A key} → k # t₁ → k # t₂ → (@0 rec : Acc _≺ₗₑₓ_ (t₁ , t₂)) → k # (merge′ t₁ t₂ rec)
  merge′-# #-nil #-nil _ = #-nil
  merge′-# #-nil k#t₂@(#-node _) _ = k#t₂
  merge′-# k#t₁@(#-node _) #-nil _ = k#t₁
  merge′-# {t₁ = node x₁ _ _ _} {t₂ = node x₂ _ _ _} (#-node _) (#-node _) _ with total (key x₁) (key x₂)
  merge′-#
    {t₁ = t₁@(node x₁ n₁ tₗ tᵣ)} {t₂ = t₂}
    (#-node k≤k₁) _ (acc rec)
    | inj₁ k₁≤k₂ with merge′ tᵣ t₂ (rec (tᵣ , t₂) (inj₁ ≺-base))
  ... | tᵣ′ with ℕ.≤-total (size tᵣ′) (size tₗ)
  ... | inj₁ _ = #-node k≤k₁
  ... | inj₂ _ = #-node k≤k₁
  merge′-#
    {t₁ = t₁} {t₂@(node x₂ n₂ tₗ tᵣ)}
    _ (#-node k≤k₂) (acc rec)
    | inj₂ k₂≤k₁ with merge′ t₁ tᵣ (rec (t₁ , tᵣ) (inj₂ (refl , ≺-base)))
  ... | tᵣ′ with ℕ.≤-total (size tᵣ′) (size tₗ)
  ... | inj₁ _ = #-node k≤k₂
  ... | inj₂ _ = #-node k≤k₂

  merge′-heap : ∀ {t₁ t₂ : Tree A key} → Heap t₁ → Heap t₂ → (@0 rec : Acc _≺ₗₑₓ_ (t₁ , t₂)) → Heap (merge′ t₁ t₂ rec)
  merge′-heap heap-nil heap-nil _ = heap-nil
  merge′-heap heap-nil h₂@(heap-node _ _ _ _) _ = h₂
  merge′-heap h₁@(heap-node _ _ _ _) heap-nil _ = h₁
  merge′-heap {t₁ = node x₁ _ _ _} {t₂ = node x₂ _ _ _} (heap-node _ _ _ _) (heap-node _ _ _ _) _ with total (key x₁) (key x₂)
  merge′-heap
    {t₁ = t₁@(node x₁ n₁ tₗ tᵣ)} {t₂ = t₂}
    (heap-node k₁#tₗ k₁#tᵣ hₗ hᵣ) h₂ (acc rec)
    | inj₁ k₁≤k₂ with merge′ tᵣ t₂ (rec (tᵣ , t₂) (inj₁ ≺-base))
                    | merge′-heap hᵣ h₂ (rec (tᵣ , t₂) (inj₁ ≺-base))
                    | merge′-# k₁#tᵣ (#-node k₁≤k₂) (rec (tᵣ , t₂) (inj₁ ≺-base))
  ... | tᵣ′ | hᵣ′ | k₁#tᵣ′ with ℕ.≤-total (size tᵣ′) (size tₗ)
  ... | inj₁ _ = heap-node k₁#tₗ k₁#tᵣ′ hₗ hᵣ′
  ... | inj₂ _ = heap-node k₁#tᵣ′ k₁#tₗ hᵣ′ hₗ
  merge′-heap
    {t₁ = t₁} {t₂@(node x₂ n₂ tₗ tᵣ)}
    h₁ (heap-node k₂#tₗ k₂#tᵣ hₗ hᵣ) (acc rec)
    | inj₂ k₂≤k₁ with merge′ t₁ tᵣ (rec (t₁ , tᵣ) (inj₂ (refl , ≺-base)))
                    | merge′-heap h₁ hᵣ (rec (t₁ , tᵣ) (inj₂ (refl , ≺-base)))
                    | merge′-# (#-node k₂≤k₁) k₂#tᵣ (rec (t₁ , tᵣ) (inj₂ (refl , ≺-base)))
  ... | tᵣ′ | hᵣ′ | k₂#tᵣ′ with ℕ.≤-total (size tᵣ′) (size tₗ)
  ... | inj₁ _ = heap-node k₂#tₗ k₂#tᵣ′ hₗ hᵣ′
  ... | inj₂ _ = heap-node k₂#tᵣ′ k₂#tₗ hᵣ′ hₗ

  merge : Tree A key → Tree A key → Tree A key
  merge t₁ t₂ = merge′ t₁ t₂ (≺ₗₑₓ-wellFounded _)

  merge-leftist : ∀ {t₁ t₂ : Tree A key} → Leftist t₁ → Leftist t₂ → Leftist (merge t₁ t₂)
  merge-leftist l₁ l₂ = merge′-leftist l₁ l₂ (≺ₗₑₓ-wellFounded _)

  merge-heap : ∀ {t₁ t₂ : Tree A key} → Heap t₁ → Heap t₂ → Heap (merge t₁ t₂)
  merge-heap h₁ h₂ = merge′-heap h₁ h₂ (≺ₗₑₓ-wellFounded _)

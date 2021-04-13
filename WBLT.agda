open import Level using (Level; _⊔_; 0ℓ)
open import Data.Product
open import Data.Product.Relation.Binary.Lex.Strict
open import Data.Sum
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality.Core
open import Induction.WellFounded

import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ

module WBLT {a ℓ₁ ℓ₂} (decTotalOrder : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder decTotalOrder renaming (Carrier to P) hiding (refl)

private
  variable
    b : Level

data Tree (A : Set b) : Set (a ⊔ b) where
  nil : Tree A
  branch : ∀ (p : P) (x : A) (n : ℕ) (hₗ : Tree A) (hᵣ : Tree A) → Tree A

module _ {A : Set b} where
  size : Tree A → ℕ
  size nil = 0
  size (branch p x n hₗ hᵣ) = n

  data Leftist : Tree A → Set where
    leftist-nil : Leftist nil
    leftist-branch : ∀ {p x n hₗ hᵣ} →
                     n ≡ suc (size hₗ + size hᵣ) →
                     size hₗ ℕ.≥ size hᵣ →
                     Leftist hₗ →
                     Leftist hᵣ →
                     Leftist (branch p x n hₗ hᵣ)
  
  data _#_ (p : P) : Tree A → Set ℓ₂ where
    #-nil : p # nil
    #-branch : ∀ {p' x n hₗ hᵣ} → p ≤ p' → p # branch p' x n hₗ hᵣ
  
  data Heap : Tree A → Set ℓ₂ where
    heap-nil : Heap nil
    heap-branch : ∀ {p x n hₗ hᵣ} → p # hₗ → p # hᵣ → Heap hₗ → Heap hᵣ → Heap (branch p x n hₗ hᵣ)

  data _≺_ : Rel (Tree A) 0ℓ where
    ≺-base : ∀ {p x n hₗ hᵣ} → hᵣ ≺ branch p x n hₗ hᵣ
    ≺-ind : ∀ {p x n h hₗ hᵣ} → h ≺ hᵣ → h ≺ branch p x n hₗ hᵣ
  
  ≺-wellFounded : WellFounded _≺_
  ≺-wellFounded′ : ∀ h → WfRec _≺_ (Acc _≺_) h
  ≺-wellFounded h = acc (≺-wellFounded′ h)
  ≺-wellFounded′ nil _ ()
  ≺-wellFounded′ (branch p x n hₗ hᵣ) hᵣ ≺-base = ≺-wellFounded hᵣ
  ≺-wellFounded′ (branch p x n hₗ hᵣ) h (≺-ind h≺hᵣ) = ≺-wellFounded′ hᵣ h h≺hᵣ

  _≺ₗₑₓ_ : Rel (Tree A × Tree A) (a ⊔ b)
  _≺ₗₑₓ_ = ×-Lex _≡_ _≺_ _≺_
  
  ≺ₗₑₓ-wellFounded : WellFounded _≺ₗₑₓ_
  ≺ₗₑₓ-wellFounded = ×-wellFounded ≺-wellFounded ≺-wellFounded
  
  merge′ : ∀ (h₁ h₂ : Tree A) → Acc _≺ₗₑₓ_ (h₁ , h₂) → Tree A
  merge′ nil nil _ = nil
  merge′ nil h@(branch _ _ _ _ _) _ = h
  merge′ h@(branch _ _ _ _ _) nil _ = h
  merge′ h₁@(branch p₁ _ _ _ _) h₂@(branch p₂ _ _ _ _) _ with total p₁ p₂
  merge′ h₁@(branch p₁ x₁ n₁ hₗ hᵣ) h₂ (acc rec) | inj₁ _ with merge′ hᵣ h₂ (rec (hᵣ , h₂) (inj₁ ≺-base))
  ... | hᵣ′ with ℕ.≤-total (size hᵣ′) (size hₗ)
  ... | inj₁ _ = branch p₁ x₁ (suc (size hₗ + size hᵣ′)) hₗ hᵣ′
  ... | inj₂ _ = branch p₁ x₁ (suc (size hᵣ′ + size hₗ)) hᵣ′ hₗ
  merge′ h₁ h₂@(branch p₂ x₂ n₂ hₗ hᵣ) (acc rec) | inj₂ _ with merge′ h₁ hᵣ ((rec (h₁ , hᵣ) (inj₂ (refl , ≺-base))))
  ... | hᵣ′ with ℕ.≤-total (size hᵣ′) (size hₗ)
  ... | inj₁ _ = branch p₂ x₂ (suc (size hₗ + size hᵣ′)) hₗ hᵣ′
  ... | inj₂ _ = branch p₂ x₂ (suc (size hᵣ′ + size hₗ)) hᵣ′ hₗ
  
  merge′-leftist : ∀ {h₁ h₂ : Tree A} → Leftist h₁ → Leftist h₂ → (rec : Acc _≺ₗₑₓ_ (h₁ , h₂)) → Leftist (merge′ h₁ h₂ rec)
  merge′-leftist leftist-nil leftist-nil _ = leftist-nil
  merge′-leftist leftist-nil lst₂@(leftist-branch _ _ _ _) _ = lst₂
  merge′-leftist lst₁@(leftist-branch _ _ _ _) leftist-nil _ = lst₁
  merge′-leftist {h₁ = branch p₁ _ _ _ _} {h₂ = branch p₂ _ _ _ _} (leftist-branch _ _ _ _) (leftist-branch _ _ _ _) _ with total p₁ p₂
  merge′-leftist
    {h₁ = h₁@(branch p₁ x₁ n₁ hₗ hᵣ)} {h₂ = h₂}
    (leftist-branch _ _ lstₗ lstᵣ) lst₂ (acc rec)
    | inj₁ _ with merge′ hᵣ h₂ (rec (hᵣ , h₂) (inj₁ ≺-base)) | merge′-leftist lstᵣ lst₂ (rec (hᵣ , h₂) (inj₁ ≺-base))
  ... | hᵣ′ | lstᵣ′ with ℕ.≤-total (size hᵣ′) (size hₗ)
  ... | inj₁ size[hₗ]≥size[hᵣ′] = leftist-branch refl size[hₗ]≥size[hᵣ′] lstₗ lstᵣ′
  ... | inj₂ size[hᵣ′]≥size[hₗ] = leftist-branch refl size[hᵣ′]≥size[hₗ] lstᵣ′ lstₗ
  merge′-leftist
    {h₁ = h₁} {h₂ = h₂@(branch p₂ x₂ n₂ hₗ hᵣ)}
    lst₁ (leftist-branch _ _ lstₗ lstᵣ) (acc rec)
    | inj₂ _ with merge′ h₁ hᵣ (rec (h₁ , hᵣ) (inj₂ (refl , ≺-base))) | merge′-leftist lst₁ lstᵣ (rec (h₁ , hᵣ) (inj₂ (refl , ≺-base)))
  ... | hᵣ′ | lstᵣ′ with ℕ.≤-total (size hᵣ′) (size hₗ)
  ... | inj₁ size[hₗ]≥size[hᵣ′] = leftist-branch refl size[hₗ]≥size[hᵣ′] lstₗ lstᵣ′
  ... | inj₂ size[hᵣ′]≥size[hₗ] = leftist-branch refl size[hᵣ′]≥size[hₗ] lstᵣ′ lstₗ
  
  merge′-# : ∀ {p : P} {h₁ h₂ : Tree A} → p # h₁ → p # h₂ → (rec : Acc _≺ₗₑₓ_ (h₁ , h₂)) → p # (merge′ h₁ h₂ rec)
  merge′-# #-nil #-nil _ = #-nil
  merge′-# #-nil p#h₂@(#-branch _) _ = p#h₂
  merge′-# p#h₁@(#-branch _) #-nil _ = p#h₁
  merge′-# {h₁ = branch p₁ _ _ _ _} {h₂ = branch p₂ _ _ _ _} (#-branch _) (#-branch _) _ with total p₁ p₂
  merge′-#
    {h₁ = h₁@(branch p₁ x₁ n₁ hₗ hᵣ)} {h₂ = h₂}
    (#-branch p≤p₁) _ (acc rec)
    | inj₁ p₁≤p₂ with merge′ hᵣ h₂ (rec (hᵣ , h₂) (inj₁ ≺-base))
  ... | hᵣ′ with ℕ.≤-total (size hᵣ′) (size hₗ)
  ... | inj₁ _ = #-branch p≤p₁
  ... | inj₂ _ = #-branch p≤p₁
  merge′-#
    {h₁ = h₁} {h₂@(branch p₂ x₂ n₂ hₗ hᵣ)}
    _ (#-branch p≤p₂) (acc rec)
    | inj₂ p₂≤p₁ with merge′ h₁ hᵣ (rec (h₁ , hᵣ) (inj₂ (refl , ≺-base)))
  ... | hᵣ′ with ℕ.≤-total (size hᵣ′) (size hₗ)
  ... | inj₁ _ = #-branch p≤p₂
  ... | inj₂ _ = #-branch p≤p₂
  
  merge′-heap : ∀ {h₁ h₂ : Tree A} → Heap h₁ → Heap h₂ → (rec : Acc _≺ₗₑₓ_ (h₁ , h₂)) → Heap (merge′ h₁ h₂ rec)
  merge′-heap heap-nil heap-nil _ = heap-nil
  merge′-heap heap-nil heap₂@(heap-branch _ _ _ _) _ = heap₂
  merge′-heap heap₁@(heap-branch _ _ _ _) heap-nil _ = heap₁
  merge′-heap {h₁ = branch p₁ _ _ _ _} {h₂ = branch p₂ _ _ _ _} (heap-branch _ _ _ _) (heap-branch _ _ _ _) _ with total p₁ p₂
  merge′-heap
    {h₁ = h₁@(branch p₁ x₁ n₁ hₗ hᵣ)} {h₂ = h₂}
    (heap-branch p₁#hₗ p₁#hᵣ heapₗ heapᵣ) heap₂ (acc rec)
    | inj₁ p₁≤p₂ with merge′ hᵣ h₂ (rec (hᵣ , h₂) (inj₁ ≺-base))
                    | merge′-heap heapᵣ heap₂ (rec (hᵣ , h₂) (inj₁ ≺-base))
                    | merge′-# p₁#hᵣ (#-branch p₁≤p₂) (rec (hᵣ , h₂) (inj₁ ≺-base))
  ... | hᵣ′ | heapᵣ′ | p₁#hᵣ′ with ℕ.≤-total (size hᵣ′) (size hₗ)
  ... | inj₁ _ = heap-branch p₁#hₗ p₁#hᵣ′ heapₗ heapᵣ′
  ... | inj₂ _ = heap-branch p₁#hᵣ′ p₁#hₗ heapᵣ′ heapₗ
  merge′-heap
    {h₁ = h₁} {h₂@(branch p₂ x₂ n₂ hₗ hᵣ)}
    heap₁ (heap-branch p₂#hₗ p₂#hᵣ heapₗ heapᵣ) (acc rec)
    | inj₂ p₂≤p₁ with merge′ h₁ hᵣ (rec (h₁ , hᵣ) (inj₂ (refl , ≺-base)))
                    | merge′-heap heap₁ heapᵣ (rec (h₁ , hᵣ) (inj₂ (refl , ≺-base)))
                    | merge′-# (#-branch p₂≤p₁) p₂#hᵣ (rec (h₁ , hᵣ) (inj₂ (refl , ≺-base)))
  ... | hᵣ′ | heapᵣ′ | p₂#hᵣ′ with ℕ.≤-total (size hᵣ′) (size hₗ)
  ... | inj₁ _ = heap-branch p₂#hₗ p₂#hᵣ′ heapₗ heapᵣ′
  ... | inj₂ _ = heap-branch p₂#hᵣ′ p₂#hₗ heapᵣ′ heapₗ
  
  merge : Tree A → Tree A → Tree A
  merge h₁ h₂ = merge′ h₁ h₂ (≺ₗₑₓ-wellFounded _)

  merge-leftist : ∀ {h₁ h₂ : Tree A} → Leftist h₁ → Leftist h₂ → Leftist (merge h₁ h₂)
  merge-leftist lst₁ lst₂ = merge′-leftist lst₁ lst₂ (≺ₗₑₓ-wellFounded _)
  
  merge-heap : ∀ {h₁ h₂ : Tree A} → Heap h₁ → Heap h₂ → Heap (merge h₁ h₂)
  merge-heap heap₁ heap₂ = merge′-heap heap₁ heap₂ (≺ₗₑₓ-wellFounded _)
  
record WBLT (A : Set b) : Set (a ⊔ b ⊔ ℓ₂) where
  constructor wblt
  field
    tree : Tree A
    leftist : Leftist tree
    heap : Heap tree

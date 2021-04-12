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
  empty : Tree A
  empty = nil

  singleton : P → A → Tree A
  singleton p x = branch p x 1 nil nil

  size : Tree A → ℕ
  size nil = 0
  size (branch p x n hₗ hᵣ) = n

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
  merge′ h₁@(branch p₁ _ _ _ _) h₂@(branch p₂ _ _ _ _) ac with p₁ ≤? p₂
  merge′ h₁@(branch p₁ x₁ n₁ hₗ hᵣ) h₂ (acc rec) | yes p₁≤p₂ with merge′ hᵣ h₂ (rec (hᵣ , h₂) (inj₁ ≺-base))
  ... | hᵣ' = if does (n₁ ℕ.≥? size hᵣ')
    then branch p₁ x₁ (suc (n₁ + size hᵣ')) h₁ hᵣ'
    else branch p₁ x₁ (suc (size hᵣ' + n₁)) hᵣ' h₁
  merge′ h₁ h₂@(branch p₂ x₂ n₂ hₗ hᵣ) (acc rec) | no p₁≰p₂ with merge′ h₁ hᵣ ((rec (h₁ , hᵣ) (inj₂ (refl , ≺-base))))
  ... | hᵣ' = if does (n₂ ℕ.≥? size hᵣ')
    then branch p₂ x₂ (suc (n₂ + size hᵣ')) hₗ hᵣ'
    else branch p₂ x₂ (suc (size hᵣ' + n₂)) hᵣ' h₁
  
  merge : Tree A → Tree A → Tree A
  merge h₁ h₂ = merge′ h₁ h₂ (≺ₗₑₓ-wellFounded (h₁ , h₂))

  data Leftist : Tree A → Set where
    leftist-nil : Leftist nil
    leftist-branch : ∀ {p x n hₗ hᵣ} → n ≡ suc (size hₗ + size hᵣ) → size hₗ ℕ.≥ size hᵣ → Leftist (branch p x n hₗ hᵣ)
  
  data _#_ (p : P) : Tree A → Set ℓ₂ where
    #-nil : p # nil
    #-branch : ∀ {p' x n hₗ hᵣ} → p ≤ p' → p # branch p' x n hₗ hᵣ
  
  data Heap : Tree A → Set ℓ₂ where
    heap-nil : Heap nil
    heap-branch : ∀ {p x n hₗ hᵣ} → p # hₗ → p # hᵣ → Heap hₗ → Heap hᵣ → Heap (branch p x n hₗ hᵣ)
  
record WBLT (A : Set b) : Set (a ⊔ b ⊔ ℓ₂) where
  constructor wblt
  field
    tree : Tree A
    leftist : Leftist tree
    heap : Heap tree

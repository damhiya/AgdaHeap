open import Level using (Level; _⊔_; 0ℓ)
open import Data.Product
open import Data.Product.Relation.Binary.Lex.Strict
open import Data.Sum
open import Data.Bool hiding (_≤?_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality.Core
open import Induction.WellFounded

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

  data _≺_ : Rel (Tree A) 0ℓ where
    ≺-base : ∀ {p x n hₗ hᵣ} → hᵣ ≺ branch p x n hₗ hᵣ
    ≺-ind : ∀ {p x n h hₗ hᵣ} → h ≺ hᵣ → h ≺ branch p x n hₗ hᵣ
  
  ≺-wellFounded : WellFounded _≺_
  ≺-wellFounded′ : (h : Tree A) → WfRec _≺_ (Acc _≺_) h
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
  merge′ h₁@(branch p₁ x₁ _ hₗ hᵣ) h₂ (acc wf) | yes p₁≤p₂ = merge′ hᵣ h₂ (wf (hᵣ , h₂) (inj₁ ≺-base))
  merge′ h₁ h₂@(branch p₂ x₂ _ hₗ hᵣ) (acc wf) | no  p₁≰p₂ = merge′ h₁ hᵣ ((wf (h₁ , hᵣ) (inj₂ (refl , ≺-base))))
  
  merge : Tree A → Tree A → Tree A
  merge h₁ h₂ = merge′ h₁ h₂ (≺ₗₑₓ-wellFounded (h₁ , h₂))

{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_; 0ℓ)
open import Function.Base
open import Data.Product
open import Data.Product.Relation.Binary.Lex.Strict
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base
open import Data.Maybe.Base as Maybe
open import Data.Bool hiding (_≤_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.List hiding (null; merge)
open import Data.List.Relation.Unary.Linked
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.Construct.Closure.Transitive as TransitiveClosure
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
  count : Tree A key → ℕ
  count nil = 0
  count (node _ _ tₗ tᵣ) = suc (count tₗ + count tᵣ)

  size : Tree A key → ℕ
  size nil = 0
  size (node _ n _ _) = n

  null : Tree A key → Bool
  null nil = true
  null (node _ _ _ _) = false

  root : Tree A key → Maybe A
  root nil = nothing
  root (node x _ _ _) = just x

  data Leftist : Tree A key → Set b where
    leftist-nil : Leftist nil
    leftist-node : ∀ {x n tₗ tᵣ} →
                     n ≡ suc (size tₗ + size tᵣ) →
                     size tₗ ℕ.≥ size tᵣ →
                     Leftist tₗ →
                     Leftist tᵣ →
                     Leftist (node x n tₗ tᵣ)

  data _#_ (k : K) : Tree A key → Set (b ⊔ ℓ₂) where
    #-nil : k # nil
    #-node : ∀ {x n tₗ tᵣ} → k ≤ key x → k # node x n tₗ tᵣ

  data Heap : Tree A key → Set (b ⊔ ℓ₂) where
    heap-nil : Heap nil
    heap-node : ∀ {x n tₗ tᵣ} →
                key x # tₗ →
                key x # tᵣ →
                Heap tₗ →
                Heap tᵣ →
                Heap (node x n tₗ tᵣ)

  Leftist⇒size≡count : ∀ {t : Tree A key} → Leftist t → size t ≡ count t
  Leftist⇒size≡count leftist-nil = refl
  Leftist⇒size≡count (leftist-node {n = n} n≡1+size[tₗ]+size[tᵣ] _ lₗ lᵣ) =
    subst₂ (((n ≡_) ∘ suc) ∘₂ _+_) (Leftist⇒size≡count lₗ) (Leftist⇒size≡count lᵣ) n≡1+size[tₗ]+size[tᵣ]

  -- data Right : Rel (Tree A key) b where
  --   right : ∀ {x n tₗ tᵣ} → Right tᵣ (node x n tₗ tᵣ)

  data _≺_ : Rel (Tree A key) b where
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

  open ≡-Reasoning
  merge′-count : ∀ (t₁ t₂ : Tree A key) → (@0 rec : Acc _≺ₗₑₓ_ (t₁ , t₂)) → count (merge′ t₁ t₂ rec) ≡ count t₁ + count t₂
  merge′-count nil nil _ = refl
  merge′-count nil t@(node _ _ _ _) _ = refl
  merge′-count t@(node _ _ tₗ tᵣ) nil _ = sym (ℕ.+-identityʳ (count t))
  merge′-count t₁@(node x₁ _ _ _) h₂@(node x₂ _ _ _) _ with total (key x₁) (key x₂)
  merge′-count t₁@(node x₁ n₁ tₗ tᵣ) t₂ (acc rec) | inj₁ _ with merge′ tᵣ t₂ (rec (tᵣ , t₂) (inj₁ ≺-base))
                                                              | merge′-count tᵣ t₂ (rec (tᵣ , t₂) (inj₁ ≺-base))
  ... | tᵣ′ | count[tᵣ′]≡count[tᵣ]+count[t₂] with ℕ.≤-total (size tᵣ′) (size tₗ)
  ... | inj₁ _ = begin
    suc (count tₗ + count tᵣ′) ≡⟨ cong (suc ∘ (count tₗ +_)) count[tᵣ′]≡count[tᵣ]+count[t₂] ⟩
    suc (count tₗ + (count tᵣ + count t₂)) ≡˘⟨ cong suc (ℕ.+-assoc (count tₗ) (count tᵣ) (count t₂)) ⟩
    suc ((count tₗ + count tᵣ) + count t₂) ∎
  ... | inj₂ _ = begin
    suc (count tᵣ′ + count tₗ) ≡⟨ cong suc (ℕ.+-comm (count tᵣ′) (count tₗ)) ⟩
    suc (count tₗ + count tᵣ′) ≡⟨ cong (suc ∘ (count tₗ +_)) count[tᵣ′]≡count[tᵣ]+count[t₂] ⟩
    suc (count tₗ + (count tᵣ + count t₂)) ≡˘⟨ cong suc (ℕ.+-assoc (count tₗ) (count tᵣ) (count t₂)) ⟩
    suc ((count tₗ + count tᵣ) + count t₂) ∎
  merge′-count t₁ t₂@(node x₂ n₂ tₗ tᵣ) (acc rec) | inj₂ _ with merge′ t₁ tᵣ ((rec (t₁ , tᵣ) (inj₂ (refl , ≺-base))))
                                                              | merge′-count t₁ tᵣ ((rec (t₁ , tᵣ) (inj₂ (refl , ≺-base))))
  ... | tᵣ′ | count[tᵣ′]≡count[t₁]+count[tᵣ] with ℕ.≤-total (size tᵣ′) (size tₗ)
  ... | inj₁ _ = begin
    suc (count tₗ + count tᵣ′) ≡⟨ cong (suc ∘ (count tₗ +_)) count[tᵣ′]≡count[t₁]+count[tᵣ] ⟩
    suc (count tₗ + (count t₁ + count tᵣ)) ≡˘⟨ cong suc (ℕ.+-assoc (count tₗ) (count t₁) (count tᵣ)) ⟩
    suc ((count tₗ + count t₁) + count tᵣ) ≡⟨ cong (suc ∘ (_+ count tᵣ)) (ℕ.+-comm (count tₗ) (count t₁)) ⟩
    suc ((count t₁ + count tₗ) + count tᵣ) ≡⟨ cong suc (ℕ.+-assoc (count t₁) (count tₗ) (count tᵣ)) ⟩
    suc (count t₁ + (count tₗ + count tᵣ)) ≡˘⟨ ℕ.+-suc (count t₁) (count tₗ + count tᵣ) ⟩
    count t₁ + suc (count tₗ + count tᵣ) ∎
  ... | inj₂ _ = begin
    suc (count tᵣ′ + count tₗ) ≡⟨ cong suc (ℕ.+-comm (count tᵣ′) (count tₗ)) ⟩
    suc (count tₗ + count tᵣ′) ≡⟨ cong (suc ∘ (count tₗ +_)) count[tᵣ′]≡count[t₁]+count[tᵣ] ⟩
    suc (count tₗ + (count t₁ + count tᵣ)) ≡˘⟨ cong suc (ℕ.+-assoc (count tₗ) (count t₁) (count tᵣ)) ⟩
    suc ((count tₗ + count t₁) + count tᵣ) ≡⟨ cong (suc ∘ (_+ count tᵣ)) (ℕ.+-comm (count tₗ) (count t₁)) ⟩
    suc ((count t₁ + count tₗ) + count tᵣ) ≡⟨ cong suc (ℕ.+-assoc (count t₁) (count tₗ) (count tᵣ)) ⟩
    suc (count t₁ + (count tₗ + count tᵣ)) ≡˘⟨ ℕ.+-suc (count t₁) (count tₗ + count tᵣ) ⟩
    count t₁ + suc (count tₗ + count tᵣ) ∎

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

  merge′-size : ∀ {t₁ t₂ : Tree A key} → Leftist t₁ → Leftist t₂ → (@0 rec : Acc _≺ₗₑₓ_ (t₁ , t₂)) → size (merge′ t₁ t₂ rec) ≡ size t₁ + size t₂
  merge′-size {t₁ = t₁} {t₂ = t₂} l₁ l₂ rec = begin
    size (merge′ t₁ t₂ rec) ≡⟨ Leftist⇒size≡count (merge′-leftist l₁ l₂ rec) ⟩
    count (merge′ t₁ t₂ rec) ≡⟨ merge′-count t₁ t₂ rec ⟩
    count t₁ + count t₂ ≡˘⟨ cong₂ _+_ (Leftist⇒size≡count l₁) (Leftist⇒size≡count l₂) ⟩
    size t₁ + size t₂ ∎

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

  merge-count : ∀ (t₁ t₂ : Tree A key) → count (merge t₁ t₂) ≡ count t₁ + count t₂
  merge-count t₁ t₂ = merge′-count t₁ t₂ (≺ₗₑₓ-wellFounded _)

  merge-leftist : ∀ {t₁ t₂ : Tree A key} → Leftist t₁ → Leftist t₂ → Leftist (merge t₁ t₂)
  merge-leftist l₁ l₂ = merge′-leftist l₁ l₂ (≺ₗₑₓ-wellFounded _)

  merge-size : ∀ {t₁ t₂ : Tree A key} → Leftist t₁ → Leftist t₂ → size (merge t₁ t₂) ≡ size t₁ + size t₂
  merge-size l₁ l₂ = merge′-size l₁ l₂ (≺ₗₑₓ-wellFounded _)

  merge-# : ∀ {k : K} {t₁ t₂ : Tree A key} → k # t₁ → k # t₂ → k # merge t₁ t₂
  merge-# k#t₁ k#t₂ = merge′-# k#t₁ k#t₂ (≺ₗₑₓ-wellFounded _)

  merge-heap : ∀ {t₁ t₂ : Tree A key} → Heap t₁ → Heap t₂ → Heap (merge t₁ t₂)
  merge-heap h₁ h₂ = merge′-heap h₁ h₂ (≺ₗₑₓ-wellFounded _)

  module _ {x₁ n₁ tₗ₁ tᵣ₁} {x₂ n₂ tₗ₂ tᵣ₂} where
    x′ : A
    x′ with total (key x₁) (key x₂)
    ... | inj₁ _ = x₁
    ... | inj₂ _ = x₂

    t₁ : Tree A key
    t₁ = node x₁ n₁ tₗ₁ tᵣ₁

    t₂ : Tree A key
    t₂ = node x₂ n₂ tₗ₂ tᵣ₂

    merge′-node : (@0 rec : Acc _≺ₗₑₓ_ (t₁ , t₂)) → ∃[ n′ ] ∃[ tₗ′ ] ∃[ tᵣ′ ] merge′ t₁ t₂ rec ≡ node x′ n′ tₗ′ tᵣ′
    merge′-node _ with total (key x₁) (key x₂)
    merge′-node (acc rs) | inj₁ _ with merge′ tᵣ₁ t₂ (rs _ (inj₁ ≺-base))
    ... | tᵣ′ with ℕ.≤-total (size tᵣ′) (size tₗ₁)
    ... | inj₁ _ = _ , _ , _ , refl
    ... | inj₂ _ = _ , _ , _ , refl
    merge′-node (acc rs) | inj₂ _ with merge′ t₁ tᵣ₂ (rs _ (inj₂ (refl , ≺-base)))
    ... | tᵣ′ with ℕ.≤-total (size tᵣ′) (size tₗ₂)
    ... | inj₁ _ = _ , _ , _ , refl
    ... | inj₂ _ = _ , _ , _ , refl

    merge-node : ∃[ n′ ] ∃[ tₗ′ ] ∃[ tᵣ′ ] merge t₁ t₂ ≡ node x′ n′ tₗ′ tᵣ′
    merge-node = merge′-node (≺ₗₑₓ-wellFounded _)

  popMin : Tree A key → Maybe (A × Tree A key)
  popMin nil = nothing
  popMin (node x _ tₗ tᵣ) = just (x , merge tₗ tᵣ)

  deleteMin : Tree A key → Maybe (Tree A key)
  deleteMin = Maybe.map proj₂ ∘ popMin

  deleteMin-count : (t₁ t₂ : Tree A key) → just t₁ ≡ deleteMin t₂ → suc (count t₁) ≡ count t₂
  deleteMin-count _ nil ()
  deleteMin-count .(merge tₗ tᵣ) (node _ _ tₗ tᵣ) refl = cong suc (merge-count tₗ tᵣ)

  DeleteMin : Rel (Tree A key) b
  DeleteMin = just -⟨ _≡_ ⟩- deleteMin

  count⇒Acc-DeleteMin : ∀ {n} (t : Tree A key) → count t ≡ n → Acc DeleteMin t
  count⇒Acc-DeleteMin nil _ = acc λ _ ()
  count⇒Acc-DeleteMin {n = suc n} t@(node _ _ _ _) refl = acc λ t' just[t']≡deleteMin[t] →
    count⇒Acc-DeleteMin {n = n} t' (ℕ.+-cancelˡ-≡ 1 (deleteMin-count t' t just[t']≡deleteMin[t]))

  DeleteMin-wellFounded : WellFounded DeleteMin
  DeleteMin-wellFounded t = count⇒Acc-DeleteMin t refl

  toList′ : ∀ (t : Tree A key) → (@0 rec : Acc DeleteMin t) → List A
  toList′ nil _ = []
  toList′ t@(node x _ tₗ tᵣ) (acc rec) = x ∷ toList′ (merge tₗ tᵣ) (rec _ refl)

  toList′-node : ∀ {x n} {tₗ tᵣ : Tree A key} (@0 rec : Acc DeleteMin (node x n tₗ tᵣ)) →
                   toList′ (node x n tₗ tᵣ) rec ≡ x ∷ toList′ (merge tₗ tᵣ) (acc-inverse rec _ refl)
  toList′-node {tₗ = tₗ} {tᵣ = tᵣ} (acc rec) = refl

  toList′-sorted : ∀ {t : Tree A key} → Heap t → (@0 rec : Acc DeleteMin t) → Linked (_≤_ on key) (toList′ t rec)
  toList′-sorted heap-nil _ = []
  toList′-sorted (heap-node _ _ heap-nil heap-nil) (acc _) = [-]
  toList′-sorted {t = node x _ nil t@(node y _ _ _)}
                 (heap-node _ (#-node x≤y) heap-nil h@(heap-node _ _ _ _)) (acc rec)
                 with toList′-node (rec t refl)
  ... | toList′[t]≡y∷ys = subst (Linked (_≤_ on key) ∘ (x ∷_)) (sym toList′[t]≡y∷ys) (x≤y ∷
                          subst (Linked (_≤_ on key)) toList′[t]≡y∷ys (toList′-sorted h (rec t refl)))
  toList′-sorted {t = node x _ t@(node y _ _ _) nil}
                 (heap-node (#-node x≤y) _ h@(heap-node _ _ _ _) heap-nil) (acc rec)
                 with toList′-node (rec t refl)
  ... | toList′[t]≡y∷ys = subst (Linked (_≤_ on key) ∘ (x ∷_)) (sym toList′[t]≡y∷ys) (x≤y ∷
                          subst (Linked (_≤_ on key)) toList′[t]≡y∷ys (toList′-sorted h (rec t refl)))
  toList′-sorted {t = node x _ t₁@(node y₁ n₁ tₗ₁ tᵣ₁) t₂@(node y₂ n₂ tₗ₂ tᵣ₂)}
                 (heap-node _ _ h₁@(heap-node _ _ _ _) h₂@(heap-node _ _ _ _)) (acc rec)
                 with total (key y₁) (key y₂) | merge-node {x₁ = y₁} {n₁ = n₁} {tₗ₁ = tₗ₁} {tᵣ₁ = tᵣ₁}
                                                           {x₂ = y₂} {n₂ = n₂} {tₗ₂ = tₗ₂} {tᵣ₂ = tᵣ₂}
  ... | inj₁ _ | n′ , tₗ′ , tᵣ′ , merge[t₁,t₂]≡node[y₁,-] = {!!}
  ... | inj₂ _ | n′ , tₗ′ , tᵣ′ , merge[t₁,t₂]≡node[y₂,-] = {!!}

  toList : Tree A key → List A
  toList t = toList′ t (DeleteMin-wellFounded _)

  toList-sorted : ∀ {t : Tree A key} → Heap t → Linked (_≤_ on key) (toList t)
  toList-sorted h = toList′-sorted h (DeleteMin-wellFounded _)

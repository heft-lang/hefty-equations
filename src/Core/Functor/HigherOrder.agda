{-# OPTIONS --safe --without-K #-} 

open import Core.Functor
open import Core.Functor.NaturalTransformation

open import Relation.Unary

open import Level renaming (suc to sℓ)

module Core.Functor.HigherOrder where

-- Higher-order functors on Set. That is, functors over the category of functors
-- on Set
record HFunctor {a b} (H : (Set a → Set b) → Set a → Set b) : Set (sℓ (a ⊔ b)) where
  field
    -- H should respect functoriality
    ⦃ HF-functor ⦄ : ∀ {F} → ⦃ Functor F ⦄ → Functor (H F)

    -- A "higher-order" map, that associates natural transformations to natural
    -- transformations
    hmap : ∀ {F G} → ∀[ F ⇒ G ] → ∀[ H F ⇒ H G ]

    -- hmap should respect naturality
    hmap-natural :
      ∀ {F G}
      → ⦃ _ : Functor F ⦄ ⦃ _ : Functor G ⦄
      → (θ : ∀[ F ⇒ G ])
      → Natural θ → Natural (hmap θ)

open HFunctor ⦃...⦄ public

variable H H₁ H₂ : (Set a → Set b) → Set a → Set b

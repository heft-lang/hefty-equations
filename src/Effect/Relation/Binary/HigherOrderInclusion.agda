{-# OPTIONS --without-K #-} 

open import Effect.Base
open import Effect.Syntax.Free
open import Effect.Syntax.Hefty

open import Core.Container
open import Core.Signature
open import Core.Functor

open import Data.Product
open import Data.Sum

open import Relation.Unary

open import Function
open import Level

module Effect.Relation.Binary.HigherOrderInclusion where

record _⊑_ (η₁ η₂ : Effectᴴ) : Set₁ where
  field
    injᴴ : ∀[ ⟦ η₁ ⟧ F ⇒ ⟦ η₂ ⟧ F ]

open _⊑_ ⦃...⦄ public 

_·⊑_ : ∀ {a} {A : Set a} → (ξ₁ ξ₂ : A → Effectᴴ) → Set (a ⊔ suc 0ℓ)
ξ₁ ·⊑ ξ₂ = ∀ {x} → ξ₁ x ⊑ ξ₂ x


injectᴴ : ⦃ η₁ ⊑ η₂ ⦄ → Algebra η₁ (Hefty η₂)
injectᴴ .α v = impure (injᴴ v)  

♯ᴴ : ⦃ η₁ ⊑ η₂ ⦄ → ∀[ Hefty η₁ ⇒ Hefty η₂ ]
♯ᴴ = fold-hefty {F = Hefty _} pure injectᴴ

⊑-refl : η ⊑ η
⊑-refl = record { injᴴ = id }

⊑-trans : η₁ ⊑ η₂ → η₂ ⊑ η₃ → η₁ ⊑ η₃
⊑-trans px qx = record { injᴴ = qx .injᴴ ∘ px .injᴴ }

⊑-⊕-left : η₁ ⊑ (η₁ ⊕ η₂)
_⊑_.injᴴ ⊑-⊕-left ⟪ c , k , s ⟫ = ⟪ inj₁ c , k , s ⟫

⊑-⊕-right : η₂ ⊑ (η₁ ⊕ η₂)
_⊑_.injᴴ ⊑-⊕-right ⟪ c , k , s ⟫ = ⟪ inj₂ c , k , s ⟫

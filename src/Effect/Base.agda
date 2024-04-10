{-# OPTIONS --without-K #-} 

open import Relation.Unary

open import Core.Functor
open import Core.Container
open import Core.Signature

open import Effect.Syntax.Free
open import Effect.Syntax.Hefty

open import Data.Empty 
open import Data.Product
open import Data.Sum

open import Function hiding (_⇔_)
open import Function.Construct.Identity using (↔-id)
open import Function.Construct.Symmetry using (↔-sym)
open import Function.Construct.Composition using (_↔-∘_)

open import Relation.Binary using (Preorder)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality using (refl ; _≡_ ; subst ; sym ; trans)

open import Level

module Effect.Base where 

Effect  = Container 
Effectᴴ = Signature

↑ : Effect → Effectᴴ
↑ ε = record
  { command  = ε .shape
  ; response = ε .position
  ; fork     = λ _ → ⊥ 
  ; returns  = λ()
  }

variable ε ε₁ ε₂ ε₃ ε′ : Effect
         η η₁ η₂ η₃ η′ : Effectᴴ
         ξ ξ₁ ξ₂ ξ₃ ξ′    : Effect → Effectᴴ 

embed : ∀[ F ⊢ ⟦ ε ⟧ᶜ ⇒ ⟦ ↑ ε ⟧ F ]
embed ⟨ s , p ⟩ .reflect = s , p , λ()

embed-free : ∀[ Free ε ⇒ Hefty (↑ ε) ]
embed-free = fold-free pure λ where .αᶜ x → impure (embed x)

-- Signature/highe-order effect morphisms

record _⊑_ (η₁ η₂ : Effectᴴ) : Set₁ where
  field
    injᴴ : ∀[ ⟦ η₁ ⟧ F ⇒ ⟦ η₂ ⟧ F ]

open _⊑_ ⦃...⦄ public 

_·⊑_ : ∀ {a} {A : Set a} → (ξ₁ ξ₂ : A → Effectᴴ) → Set (a ⊔ suc 0ℓ)
ξ₁ ·⊑ ξ₂ = ∀ {x} → ξ₁ x ⊑ ξ₂ x

free-resp-⇿ : ε₁ ⇿ ε₂ → ∀[ Free ε₁ ⇒ Free ε₂ ]
free-resp-⇿ eq = hmap-free (eq .equivalence _ .Inverse.to) 

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



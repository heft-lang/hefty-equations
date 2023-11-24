open import Data.Product
open import Data.Sum

open import Function
open import Relation.Unary

open import Core.Functor

import Relation.Binary.PropositionalEquality as ≡

module Core.Container where

record Container : Set₁ where
  no-eta-equality
  field shape    : Set
        position : shape → Set

  infix 1 ⟨_⟩ 
  record ⟦_⟧ᶜ (A : Set) : Set where
    constructor ⟨_⟩
    field reflectᶜ : Σ shape λ s → position s → A

  open ⟦_⟧ᶜ public

  record Algebraᶜ (A : Set) : Set where
    field αᶜ : ⟦_⟧ᶜ A → A

  open Algebraᶜ public 

open Container public

variable C C₁ C₂ : Container

_⊕ᶜ_ : (C₁ C₂ : Container) → Container
C₁ ⊕ᶜ C₂ = record
  { shape    = C₁ .shape ⊎ C₂ .shape
  ; position = [ C₁ .position , C₂ .position ]
  }

_⟨⊕⟩ᶜ_ : ∀[ Algebraᶜ C₁ ⇒ Algebraᶜ C₂ ⇒ Algebraᶜ (C₁ ⊕ᶜ C₂) ] 
(x ⟨⊕⟩ᶜ y) .αᶜ ⟨ inj₁ s , p ⟩ = x .αᶜ ⟨ s , p ⟩
(x ⟨⊕⟩ᶜ y) .αᶜ ⟨ inj₂ s , p ⟩ = y .αᶜ ⟨ s , p ⟩

con-map : (A → B) → ⟦ C ⟧ᶜ A → ⟦ C ⟧ᶜ B 
con-map f ⟨ s , p ⟩ = ⟨ s , f ∘ p ⟩ 

instance
  con-functor : Functor ⟦ C ⟧ᶜ
  con-functor .fmap                 = con-map
  con-functor .fmap-id ⟨ s , p ⟩    = ≡.refl
  con-functor .fmap-∘ f g ⟨ s , p ⟩ = ≡.refl 

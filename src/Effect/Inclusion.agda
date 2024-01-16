open import Data.Product 

open import Core.Functor 
open import Core.Container
open import Core.Ternary 

open import Effect.Base 
open import Effect.Syntax.Free 
open import Effect.Separation

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

open import Data.Sum 

open import Function
open import Level

module Effect.Inclusion where

module R₃ = Relation Effect Union
open Union
open Inverse 

_≲_ : Rel Effect (suc 0ℓ)
_≲_ = R₃.Ext

≲-refl = R₃.Ext-reflexive (⊥ᶜ , union-unitʳ)
≲-trans = R₃.Ext-transitive union-assocʳ

≲-preorder : Preorder _ _ _
≲-preorder = R₃.Ext-preorder (⊥ᶜ , union-unitʳ) union-assocʳ 

-- some properties about effect inclusion 
module _ where

 ≲-⊕ᶜ-left : ∀ ε′ → ε ≲ (ε ⊕ᶜ ε′)
 ≲-⊕ᶜ-left ε′ = ε′ , ⊕ᶜ-union 
  
 ≲-⊕ᶜ-right : ∀ ε′ → ε ≲ (ε′ ⊕ᶜ ε)
 ≲-⊕ᶜ-right {ε} ε′ = ε′ , union-respects-⇿ .R₃.r₃ (swapᶜ-⇿ ε ε′) ⊕ᶜ-union

 ≲-∙-left : ε₁ ∙ ε₂ ≈ ε → ε₁ ≲ ε
 ≲-∙-left σ = _ , σ 

 ≲-∙-right : ε₁ ∙ ε₂ ≈ ε → ε₂ ≲ ε
 ≲-∙-right σ = _ , union-comm σ

 ≲-respects-⇿ˡ : ε₁ ⇿ ε₂ → ε₁ ≲ ε → ε₂ ≲ ε
 ≲-respects-⇿ˡ eq (ε′ , σ) = ε′ , union-respects-⇿ .R₃.r₁ eq σ

 ≲-respects-⇿ʳ : ε₁ ⇿ ε₂ → ε ≲ ε₁ → ε ≲ ε₂
 ≲-respects-⇿ʳ eq (ε′ , σ) = ε′ , union-respects-⇿ .R₃.r₃ eq σ 

-- Transforming an effect tree's signature using inclusions and separations
module _ where

  inj : ⦃ ε₁ ≲ ε₂ ⦄ → ε₁ ↦ ε₂
  inj ⦃ ε′ , u ⦄ = u .union .equivalence _ .to ∘ injˡ ε′ 

  inj-natural : ⦃ i : ε₁ ≲ ε₂ ⦄ → Natural inj
  inj-natural ⦃ i ⦄ .commute {f = f} ⟨ c , k ⟩ = i .proj₂ .union .natural .to-natural .commute {f = f} _
    
  inject : ⦃ ε₁ ≲ ε₂ ⦄ → Algebraᶜ ε₁ (Free ε₂ A)
  inject .αᶜ = impure ∘ inj

  ♯ : ⦃ ε₁ ≲ ε₂ ⦄ → ∀[ Free ε₁ ⇒ Free ε₂ ]
  ♯ = fold-free pure inject 
  
  ♯ˡ : ∀ ε₂ → ∀[ Free ε₁ ⇒ Free (ε₁ ⊕ᶜ ε₂) ]
  ♯ˡ ε₂ = ♯ ⦃ ≲-⊕ᶜ-left ε₂ ⦄

  ♯ʳ : ∀ ε₁ → ∀[ Free ε₂ ⇒ Free (ε₁ ⊕ᶜ ε₂) ]
  ♯ʳ ε₁ = ♯ ⦃ ≲-⊕ᶜ-right ε₁ ⦄

  ♯ˡ′ : (σ : ε₁ ∙ ε₂ ≈ ε) → ∀[ Free ε₁ ⇒ Free ε ]
  ♯ˡ′ σ = ♯ ⦃ ≲-∙-left σ ⦄

  ♯ʳ′ : (σ : ε₁ ∙ ε₂ ≈ ε) → ∀[ Free ε₂ ⇒ Free ε ]
  ♯ʳ′ σ = ♯ ⦃ ≲-∙-right σ ⦄

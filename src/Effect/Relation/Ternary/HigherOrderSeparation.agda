{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Functor.NaturalTransformation
open import Core.Signature
import Core.Ternary as Ternary 

open import Effect.Base

open import Data.Sum
open import Data.Product
open import Data.Empty

open import Function
open import Function.Construct.Identity
open import Function.Construct.Composition
open import Level

open import Relation.Binary.PropositionalEquality

module Effect.Relation.Ternary.HigherOrderSeparation where

record Unionᴴ (σ₁ σ₂ σ : Signature) : Set₁ where
  field
    unionᴴ : (σ₁ ⊕ σ₂) ⇿ᴴ σ

instance sig-rel₃ : Ternary.HasRel₃ Signature (suc zero)
sig-rel₃ = record { _∙_≈_ = Unionᴴ } 

instance effectᴴ-rel₃ : Ternary.HasRel₃ Effectᴴ (suc zero)
effectᴴ-rel₃ = record { _∙_≈_ = λ η₁ η₂ η → ∀ {ε} → Unionᴴ (η₁ ε) (η₂ ε) (η ε) } 

open Unionᴴ
open Inverse

-- Some properties of disjoint unions of ho effects
module _ where
  
  open Ternary
  open Ternary.Relation Effectᴴ ⦃ effectᴴ-rel₃ ⦄ 

  unionᴴ-unitˡ : LeftIdentity (λ ε → ⊥-sig)  
  unionᴴ-unitˡ .unionᴴ .equivalenceᴴ F X = record
    { to        = λ where ⟪ inj₂ c , k , s ⟫ → ⟪ c , k , s ⟫
    ; from      = λ where ⟪ c , k , s ⟫ → ⟪ inj₂ c , k , s ⟫
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   =   (λ where refl → refl)
                  , (λ where {⟪ inj₂ c , k , s ⟫} refl → refl)
    }

  unionᴴ-unitʳ : RightIdentity λ ε → ⊥-sig
  unionᴴ-unitʳ .unionᴴ .equivalenceᴴ F X = record
    { to        = λ where ⟪ inj₁ c , k , s ⟫ → ⟪ c , k , s ⟫
    ; from      = λ where ⟪ c , k , s ⟫ → ⟪ inj₁ c , k , s ⟫
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   =   (λ where refl → refl)
                  , λ where {⟪ inj₁ c , k , s ⟫} refl → refl
    }

  unionᴴ-comm : Commutative
  unionᴴ-comm u .unionᴴ .equivalenceᴴ F X = u .unionᴴ .equivalenceᴴ F X ↔-∘ swap-sig-⇿ᴴ .equivalenceᴴ _ _ 

  unionᴴ-assocʳ : RightAssociative
  unionᴴ-assocʳ {η₁} {η₂} {η₁₂} {η₃} {η₁₂₃} u₁ u₂
    = (η₂ ·⊕ η₃)
    , (λ where .unionᴴ → ⇿ᴴ-trans (⇿ᴴ-sym assoc-sig-⇿ᴴ) (⇿ᴴ-trans (⊕-congˡ (u₁ .unionᴴ)) (u₂ .unionᴴ)))
    , λ where .unionᴴ → ⇿ᴴ-refl 
  
  unionᴴ-respects-⇿ᴴ : Respects λ η₁ η₂ → ∀ {ε} → η₁ ε ⇿ᴴ η₂ ε
  unionᴴ-respects-⇿ᴴ = record
    { r₁ = λ where eq u .unionᴴ → ⇿ᴴ-trans (⊕-congˡ (⇿ᴴ-sym eq)) (u .unionᴴ) 
    ; r₂ = λ where eq u .unionᴴ → ⇿ᴴ-trans (⊕-congʳ (⇿ᴴ-sym eq)) (u .unionᴴ)
    ; r₃ = λ where eq u .unionᴴ → ⇿ᴴ-trans (u .unionᴴ) eq
    } 

  ⊕-unionᴴ : η₁ ∙ η₂ ≈ (η₁ ·⊕ η₂) 
  equivalenceᴴ (unionᴴ ⊕-unionᴴ) F X = ↔-id _

{-# OPTIONS --without-K #-} 

open import Effect.Base
open import Effect.Syntax.Free
open import Effect.Syntax.Hefty
open import Effect.Relation.Ternary.HigherOrderSeparation

open import Core.Container
open import Core.Signature
open import Core.Functor
open import Core.Ternary

open import Data.Product
open import Data.Sum

open import Relation.Unary
open import Relation.Binary using (Reflexive; Transitive)

open import Function
open import Level


module Effect.Relation.Binary.HigherOrderInclusion where

open Unionᴴ
open Inverse

module R₃ = Relation Effectᴴ ⦃ effectᴴ-rel₃ ⦄

≲ᴴ-refl : Reflexive _≲_
≲ᴴ-refl {η} = (const ⊥-sig) , (λ {ε} → unionᴴ-unitʳ {η} {ε})

≲ᴴ-trans : Transitive _≲_
≲ᴴ-trans i₁ i₂ = R₃.Ext-transitive unionᴴ-assocʳ i₁ i₂

injᴴ : ⦃ σ₁ ≲ σ₂ ⦄ → σ₁ ↦ᴴ σ₂
injᴴ ⦃ _ , u ⦄ = u .unionᴴ .equivalenceᴴ _ _ .to ∘ injᴴˡ

injectᴴ : ⦃ σ₁ ≲ σ₂ ⦄ → Algebra σ₁ (Hefty σ₂)
injectᴴ .α = impure ∘ injᴴ 

♯ᴴ : ⦃ σ₁ ≲  σ₂ ⦄ → ∀[ Hefty σ₁ ⇒ Hefty σ₂ ]
♯ᴴ = fold-hefty {F = Hefty _} pure injectᴴ

instance ho-apply : ⦃ η₁ ≲ η₂ ⦄ → ∀ {ε} → η₁ ε ≲ η₂ ε
ho-apply ⦃ _ , u ⦄ = _ , u 

postulate ⊑-⊕-left : σ₁ ≲ (σ₁ ⊕ σ₂)
postulate ·⊑-⊕-left : η₁ ≲ (η₁ ·⊕ η₂) 

postulate ⊑-⊕-right : σ₂ ≲ (σ₁ ⊕ σ₂)
postulate ·⊑-⊕-right : η₂ ≲ (η₁ ·⊕ η₂)

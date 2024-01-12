
open import Core.Container
import Core.Ternary as Ternary

open import Effect.Base 

open import Data.Sum 
open import Data.Product
open import Data.Empty

open import Relation.Unary
open import Relation.Binary.PropositionalEquality

open import Function
open import Function.Construct.Identity
open import Function.Construct.Composition

module Effect.DisjointUnion where

record Union (ε₁ ε₂ ε : Effect) : Set₁ where
  field
    union : ∀ X → ⟦ ε₁ ⊕ᶜ ε₂ ⟧ᶜ X ↔ ⟦ ε ⟧ᶜ X 

  open Inverse 

  inja : ε₁ ↦ ε 
  inja = union _ .to ∘ injˡ ε₂ 

  injb : ε₂ ↦ ε
  injb = union _ .to ∘ injʳ ε₁

  proj : ε ↦ (ε₁ ⊕ᶜ ε₂)
  proj = union _ .from

open Union
open Inverse

module _ where

  open Ternary.Relation Effect Union

  union-unitˡ : LeftIdentity ⊥ᶜ
  union-unitˡ {ε} .union _ = record
    { to        = to′
    ; from      = from′
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   = (λ _ → refl) , λ where ⟨ inj₂ c , k ⟩ → refl
    }
    where
      to′ : (⊥ᶜ ⊕ᶜ ε) ↦ ε
      to′ ⟨ inj₂ c , k ⟩ = ⟨ c , k ⟩

      from′ : ε ↦ (⊥ᶜ ⊕ᶜ ε)
      from′ ⟨ c , k ⟩ = ⟨ inj₂ c , k ⟩

  union-unitʳ : RightIdentity ⊥ᶜ
  union-unitʳ {ε} .union _ = record
    { to        = to′
    ; from      = from′
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   = (λ _ → refl) , (λ where ⟨ inj₁ c , k ⟩ → refl)
    }
    where
      to′ : (ε ⊕ᶜ ⊥ᶜ) ↦ ε
      to′ ⟨ inj₁ c , k ⟩ = ⟨ c , k ⟩

      from′ : ε ↦ (ε ⊕ᶜ ⊥ᶜ)
      from′ ⟨ c , k ⟩ = ⟨ (inj₁ c , k) ⟩ 

  union-comm : Commutative
  union-comm {ε₁} {ε₂} u .union _ = swapᶜ-↔ {ε₂} {ε₁} _ ↔-∘ u .union _ 

  union-assocʳ : RightAssociative
  union-assocʳ {ε₁} {ε₂} {ε₁₂} {ε₃} {ε₁₂₃} u₁ u₂ = (ε₂ ⊕ᶜ ε₃) , Un , λ where .union _ → id-↔ _
    where
      Un : Union ε₁ (ε₂ ⊕ᶜ ε₃) ε₁₂₃
      Un .union _ = {!!} ↔-∘ u₂ .union _ 

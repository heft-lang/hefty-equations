{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Functor.NaturalTransformation

open import Core.Container
import Core.Ternary as Ternary

open import Effect.Base 

open import Data.Sum 
open import Data.Product
open import Data.Empty

open import Relation.Unary
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])

open import Function
open import Level
open import Function.Construct.Identity using (↔-id)

module Effect.Relation.Ternary.FirstOrderSeparation where

record Union (ε₁ ε₂ ε : Effect) : Set₁ where
  field
    union  : (ε₁ ⊕ᶜ ε₂) ⇿ ε

  open Inverse 

  inja : ε₁ ↦ ε 
  inja = union .equivalence _ .to ∘ injˡ ε₂ 

  inja-natural : Natural inja
  inja-natural =
    ∘-natural (injˡ ε₂) (union .equivalence _ .to)
      (injˡ-natural {C₂ = ε₂})
      (union .natural .to-natural) 

  injb : ε₂ ↦ ε
  injb = union .equivalence _ .to ∘ injʳ ε₁

  injb-natural : Natural injb
  injb-natural =
    ∘-natural (injʳ ε₁) (union .equivalence _ .to)
      (injʳ-natural {C₁ = ε₁})
      (union .natural .to-natural) 

  proj : ε ↦ (ε₁ ⊕ᶜ ε₂)
  proj = union .equivalence _ .from

  proj⁻¹ : (ε₁ ⊕ᶜ ε₂) ↦ ε
  proj⁻¹ = union .equivalence _ .to

  proj-natural : Natural proj 
  proj-natural = union .natural .from-natural 

  proj⁻¹-natural : Natural proj⁻¹
  proj⁻¹-natural = union .natural .to-natural

instance effect-rel₃ : Ternary.HasRel₃ Effect (suc zero)
effect-rel₃ = record { _∙_≈_ = Union } 

open Union
open Inverse

-- Prove some properties about disjoint unions of effects 
module _ where

  open Ternary.Relation Effect ⦃ effect-rel₃ ⦄

  union-unitˡ : LeftIdentity ⊥ᶜ
  union-unitˡ {ε} .union .equivalence _ = record
    { to        = to′
    ; from      = from′
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   = (λ where refl → refl) , λ where {x = ⟨ inj₂ _ , _ ⟩ } refl → refl
    }
    where
      to′ : (⊥ᶜ ⊕ᶜ ε) ↦ ε
      to′ ⟨ inj₂ c , k ⟩ = ⟨ c , k ⟩

      from′ : ε ↦ (⊥ᶜ ⊕ᶜ ε)
      from′ ⟨ c , k ⟩ = ⟨ inj₂ c , k ⟩    
  union-unitˡ {ε} .union .natural  = record
    { to-natural   = λ where .commute ⟨ inj₂ c , k ⟩ → refl
    ; from-natural = λ where .commute _              → refl
    } 

  union-unitʳ : RightIdentity ⊥ᶜ
  union-unitʳ {ε} .union .equivalence _ = record
    { to        = to′
    ; from      = from′
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   = (λ where refl → refl) , (λ where {x = ⟨ inj₁ c , k ⟩} refl → refl)
    }
    where
      to′ : (ε ⊕ᶜ ⊥ᶜ) ↦ ε
      to′ ⟨ inj₁ c , k ⟩ = ⟨ c , k ⟩

      from′ : ε ↦ (ε ⊕ᶜ ⊥ᶜ)
      from′ ⟨ c , k ⟩ = ⟨ (inj₁ c , k) ⟩ 
  union-unitʳ {ε} .union .natural = record
    { to-natural   = λ where .commute ⟨ inj₁ c , k ⟩ → refl
    ; from-natural = λ where .commute _              → refl
    } 

  union-comm : Commutative
  union-comm {ε₁} {ε₂} u .union = ⇿-trans (swapᶜ-⇿ ε₂ ε₁)  (u .union)

  union-assocʳ : RightAssociative
  union-assocʳ {ε₁} {ε₂} {ε₁₂} {ε₃} {ε₁₂₃} u₁ u₂
    = (ε₂ ⊕ᶜ ε₃)
    , Un
    , λ where .union → ⇿-refl 
    where
      Un : Union ε₁ (ε₂ ⊕ᶜ ε₃) ε₁₂₃
      Un .union =
          ⇿-trans (assocᶜ-⇿ ε₁ ε₂ ε₃)
        $ ⇿-trans (⊕ᶜ-congˡ (ε₁ ⊕ᶜ ε₂) ε₁₂ ε₃ (u₁ .union)) (u₂ .union)

  union-respects-⇿ : Respects _⇿_
  union-respects-⇿ = record
    { r₁ = λ where
        {ε₁} {ε₂} {ε} eq u .union →
           ⇿-trans (⊕ᶜ-congˡ ε₂ ε₁ ε (⇿-sym eq)) (u .union)
    ; r₂ = λ where
        {ε₁} {ε₂} {ε} eq u .union →
          ⇿-trans (⊕ᶜ-congʳ ε ε₂ ε₁ (⇿-sym eq)) (u .union)
    ; r₃ = λ where
        {ε₁} {ε₂} {ε} eq u .union →
          ⇿-trans (u .union) eq
    }
  
  ⊕ᶜ-union : Union ε₁ ε₂ (ε₁ ⊕ᶜ ε₂) 
  ⊕ᶜ-union .union = record
    { equivalence = λ _ → ↔-id _
    ; natural     = record
      { to-natural   = λ where .commute _ → refl
      ; from-natural = λ where .commute _ → refl
      }
    } 

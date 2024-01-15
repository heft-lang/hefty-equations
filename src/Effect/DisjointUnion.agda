open import Core.Functor
open import Core.Container
import Core.Ternary as Ternary

open import Effect.Base 

open import Data.Sum 
open import Data.Product
open import Data.Empty

open import Relation.Unary
open import Relation.Binary.PropositionalEquality

open import Function

module Effect.DisjointUnion where

record Union (ε₁ ε₂ ε : Effect) : Set₁ where
  field
    union  : (ε₁ ⊕ᶜ ε₂) ⇿ ε

  open Inverse 

  inja : ε₁ ↦ ε 
  inja = union .equivalence _ .to ∘ injˡ ε₂ 

  injb : ε₂ ↦ ε
  injb = union .equivalence _ .to ∘ injʳ ε₁

  proj : ε ↦ (ε₁ ⊕ᶜ ε₂)
  proj = union .equivalence _ .from

open Union
open Inverse

module _ where

  open Ternary.Relation Effect Union

  union-unitˡ : LeftIdentity ⊥ᶜ
  union-unitˡ {ε} .union .equivalence _ = record
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
    ; inverse   = (λ _ → refl) , (λ where ⟨ inj₁ c , k ⟩ → refl)
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
  

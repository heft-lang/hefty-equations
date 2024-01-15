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
open import Function.Construct.Identity
open import Function.Construct.Symmetry
open import Function.Construct.Composition

module Effect.DisjointUnion where

record Union (ε₁ ε₂ ε : Effect) : Set₁ where
  field
    union  : (ε₁ ⊕ᶜ ε₂) ⇿ ε
    natiso : NaturalIsomorphism union 

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
  union-unitˡ {ε} .natiso = record
    { to-natural   = λ where .commute ⟨ inj₂ c , k ⟩ → refl
    ; from-natural = λ where .commute _              → refl
    } 

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
  union-unitʳ {ε} .natiso = record
    { to-natural   = λ where .commute ⟨ inj₁ c , k ⟩ → refl
    ; from-natural = λ where .commute _              → refl
    } 

  union-comm : Commutative
  union-comm {ε₁} {ε₂} u .union _
    = swapᶜ-↔ {ε₂} {ε₁} _ ↔-∘ u .union _
  union-comm {ε₁} {ε₂} u .natiso
    = natiso-∘ (swapᶜ-↔-natural ε₂ ε₁) (u .natiso)

  union-assocʳ : RightAssociative
  union-assocʳ {ε₁} {ε₂} {ε₁₂} {ε₃} {ε₁₂₃} u₁ u₂
    = (ε₂ ⊕ᶜ ε₃)
    , Un
    , record
        { union = λ _ → ↔-id _
        ; natiso = record
          { to-natural   = λ where .commute _ → refl
          ; from-natural = λ where .commute _ → refl
          }
        } 
    where
      Un : Union ε₁ (ε₂ ⊕ᶜ ε₃) ε₁₂₃
      Un .union _ =
            assocᶜ-↔ {ε₁} {ε₂} {ε₃} _
        ↔-∘ ( ⊕ᶜ-congˡ {ε₁ ⊕ᶜ ε₂} {ε₁₂} {ε₃} (u₁ .union) _
        ↔-∘ u₂ .union _ )
      Un .natiso =
        ( natiso-∘ (assocᶜ-natiso ε₁ ε₂ ε₃)
        ( natiso-∘ (⊕ᶜ-congˡ-natiso (ε₁ ⊕ᶜ ε₂) ε₁₂ ε₃ (u₁ .union) (u₁ .natiso))
                   (u₂ .natiso)) ) 

  {- TODO: this requires that the container isomorphism is natural -} 
  postulate union-respects-⇿ : Respects _⇿_
-- union-respects-⇿ = record
--   { r₁ = λ where
--       {c₁} {c₂} {c} eq u .union X →
--         ⊕ᶜ-congˡ {c₂} {c₁} {c} (λ X → ↔-sym (eq X)) _ ↔-∘ u .union X
--       {c₁} {c₂} {c} eq u .natiso →
--         {!!} 
--   ; r₂ = λ where
--       {c₁} {c₂} {c} eq u .union X →
--         ⊕ᶜ-congʳ {c} {c₂} {c₁} (λ X → ↔-sym (eq X)) _ ↔-∘ u .union X
--       {c₁} {c₂} {c} eq u .natiso →
--         {!!}
--   ; r₃ = λ where
--       eq u .union X → u .union X ↔-∘ eq X
--       eq u .natiso  → natiso-∘ (u .natiso)
--         {!!} 
--   } 
-- 

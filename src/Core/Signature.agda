module Core.Signature where

open import Relation.Unary
open import Function 
open import Data.Product 
open import Data.Sum

open import Core.Functor

record Signature : Set₁ where
  no-eta-equality
  field
    command  : Set
    response : command → Set

    fork     : command → Set
    returns  : {c : command} → (ψ : fork c) → Set 

  -- The reflection (extension) of a signature as an endofunctor on [set,set]. 
  record ⟦_⟧ (M : Set → Set) (A : Set) : Set where
    constructor ⟪_⟫ 
    field reflect : Σ command λ c → (response c → M A) × ((ψ : fork c) → M (returns ψ))

  open ⟦_⟧ public 

  record Algebra (F : Set → Set) : Set₁ where
    field α : ∀[ ⟦_⟧ F ⇒ F ] 

  open Algebra public 

open Signature public 

variable σ σ₁ σ₂ σ′ : Signature

_⊕_ : (_ _ : Signature) → Signature
σ₁ ⊕ σ₂ = record
  { command  = σ₁ .command ⊎ σ₂ .command
  ; response = [ σ₁ .response , σ₂ .response ]
  ; fork     = [ σ₁ .fork , σ₂ .fork ]
  ; returns  = λ where {inj₁ c} → σ₁ .returns
                       {inj₂ c} → σ₂ .returns 
  }

_⟨⊕⟩_ : ∀[ Algebra σ₁ ⇒ Algebra σ₂ ⇒ Algebra (σ₁ ⊕ σ₂) ]
(x ⟨⊕⟩ y) .α ⟪ inj₁ c , r , s ⟫ = x .α ⟪ c , r , s ⟫
(x ⟨⊕⟩ y) .α ⟪ inj₂ c , r , s ⟫ = y .α ⟪ c , r , s ⟫

-- The semantics of signatures maps functors to functors 
instance
  sig-functor : ⦃ Functor F ⦄ → Functor (⟦ σ ⟧ F)
  sig-functor .fmap f ⟪ c , r , s ⟫ = ⟪ c , fmap f ∘ r , s ⟫

  sig-hfunctor : HFunctor ⟦ σ ⟧
  sig-hfunctor .hmap θ ⟪ c , r , s ⟫ = ⟪ (c , θ ∘ r , θ ∘ s) ⟫ 

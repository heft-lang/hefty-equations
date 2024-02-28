{-# OPTIONS --without-K #-} 

open import Relation.Unary
open import Function 
open import Data.Product 
open import Data.Sum

open import Core.Functor
open import Core.Functor.NaturalTransformation
open import Core.Functor.HigherOrder
open import Core.Extensionality

import Relation.Binary.PropositionalEquality as ≡

module Core.Signature where

open ≡.≡-Reasoning

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

_·⊕_ : {A : Set a} → (_ _ : A → Signature) → A → Signature
(P ·⊕ Q) x = P x ⊕ Q x

_⟨⊕⟩_ : ∀[ Algebra σ₁ ⇒ Algebra σ₂ ⇒ Algebra (σ₁ ⊕ σ₂) ]
(x ⟨⊕⟩ y) .α ⟪ inj₁ c , r , s ⟫ = x .α ⟪ c , r , s ⟫
(x ⟨⊕⟩ y) .α ⟪ inj₂ c , r , s ⟫ = y .α ⟪ c , r , s ⟫

sig-hmap : ∀[ F ⇒ G ] → ∀[ ⟦ σ ⟧ F ⇒ ⟦ σ ⟧ G ]
sig-hmap θ ⟪ c , r , s ⟫ = ⟪ c , θ ∘ r , θ ∘ s  ⟫


-- The semantics of signatures maps functors to functors 
instance
  sig-functor : ⦃ Functor F ⦄ → Functor (⟦ σ ⟧ F)
  sig-functor .fmap f  ⟪ c , r , s ⟫ = ⟪ c , fmap f ∘ r , s ⟫
  sig-functor {F = F} .fmap-id
    = extensionality λ where ⟪ c , r , s ⟫ → ≡.cong (λ ○ → ⟪ c , ○ , s ⟫) (≡.cong (_∘ r) $ fmap-id {F = F})
  sig-functor .fmap-∘  f g =
    extensionality λ where ⟪ c , r , s ⟫ → ≡.cong (λ ○ → ⟪ c , ○ , s ⟫) (≡.cong (_∘ r) (fmap-∘ f g)) 

instance 
  sig-hfunctor : HFunctor ⟦ σ ⟧
  sig-hfunctor .HF-functor = sig-functor 
  sig-hfunctor .hmap θ ⟪ c , r , s ⟫ = ⟪ c , θ ∘ r , θ ∘ s ⟫
  sig-hfunctor .hmap-natural θ nt .commute {f = f} ⟪ c , r , s ⟫ =
    begin
      ⟪ c , θ ∘ fmap f ∘ r , θ ∘ s ⟫
    ≡⟨ ≡.cong₂ (λ ○₁ ○₂ → ⟪ c , ○₁ , ○₂ ⟫) (extensionality $ nt .commute ∘ r) ≡.refl ⟩
      ⟪ c , fmap f ∘ θ ∘ r , θ ∘ s ⟫
    ∎

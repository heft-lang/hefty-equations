
open import Relation.Unary
open import Function
open import Data.Product 

open import Core.Functor
open import Core.Signature 

module Hefty.Base where

data Hefty (σ : Signature) : Set → Set where
  pure   : ∀[ id              ⇒ Hefty σ ] 
  impure : ∀[ ⟦ σ ⟧ (Hefty σ) ⇒ Hefty σ ]

variable m m₁ m₂ m₃ m′ : Hefty σ A 

instance hefty-pointed : Pointed (Hefty σ)
hefty-pointed = record
  { point = pure
  } 

fold-hefty : ∀[ id ⇒ F ] → Algebra σ F → ∀[ Hefty σ ⇒ F ]
fold-hefty η y (pure x)                = η x
fold-hefty η y (impure ⟪ c , r , s ⟫ ) = y .α ⟪ c , fold-hefty η y ∘ r , fold-hefty η y ∘ s ⟫ 

rec-hefty : ⦃ Pointed F ⦄ → (A → F B) → Algebra σ F → Hefty σ A → F B
rec-hefty k _ (pure x)               = (k x)
rec-hefty k y (impure ⟪ c , r , s ⟫) = y . α ⟪ c , rec-hefty k y ∘ r , rec-hefty point y ∘ s ⟫

map-hefty : (A → B) → Hefty σ A → Hefty σ B
map-hefty f (pure x) = pure (f x)
map-hefty f (impure ⟪ c , r , s ⟫) = impure ⟪ c , map-hefty f ∘ r , s ⟫

bind-hefty : Hefty σ A → (A → Hefty σ B) → Hefty σ B
bind-hefty t k = rec-hefty k (λ where .α → impure) t

instance
  hefty-functor : Functor (Hefty σ)
  hefty-functor = record
    { fmap = map-hefty 
    } 

  hefty-monad : Monad (Hefty σ)
  hefty-monad = record
    { return = point
    ; _∗     = flip bind-hefty
    } 


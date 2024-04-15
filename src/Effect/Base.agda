{-# OPTIONS --without-K #-} 

open import Relation.Unary

open import Core.Functor
open import Core.Container
open import Core.Signature

open import Effect.Syntax.Free
open import Effect.Syntax.Hefty

open import Data.Empty 
open import Data.Product
open import Data.Sum

open import Function hiding (_⇔_)
open import Function.Construct.Identity using (↔-id)
open import Function.Construct.Symmetry using (↔-sym)
open import Function.Construct.Composition using (_↔-∘_)

open import Relation.Binary using (Preorder)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality using (refl ; _≡_ ; subst ; sym ; trans)

open import Level

module Effect.Base where 

Effect  = Container 
Effectᴴ = Effect → Signature

↑ : Effectᴴ
↑ ε = record
  { command  = ε .shape
  ; response = ε .position
  ; fork     = λ _ → ⊥ 
  ; returns  = λ()
  }

variable ε ε₁ ε₂ ε₃ ε′ : Effect
         η η₁ η₂ η₃ η′ : Effectᴴ

embed : ∀[ F ⊢ ⟦ ε ⟧ᶜ ⇒ ⟦ ↑ ε ⟧ F ]
embed ⟨ s , p ⟩ .reflect = s , p , λ()

embed-free : ∀[ Free ε ⇒ Hefty (↑ ε) ]
embed-free = fold-free pure λ where .αᶜ x → impure (embed x)

-- Signature/highe-order effect morphisms
free-resp-⇿ : ε₁ ⇿ ε₂ → ∀[ Free ε₁ ⇒ Free ε₂ ]
free-resp-⇿ eq = hmap-free (eq .equivalence _ .Inverse.to) 



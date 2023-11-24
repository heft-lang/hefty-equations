open import Relation.Unary

open import Core.Functor
open import Core.Container
open import Core.Signature
open import Core.DisjointUnion

open import Free.Base
open import Hefty.Base
open import Effect.Base

open import Data.Empty 
open import Data.Product
open import Data.Sum

open import Effect.Separation

open import Function hiding (_⇔_)

open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality using (refl ; _≡_ ; subst ; sym ; trans)

open import Effect.Handle

module Effect.Elaborate where

open import Core.MonotonePredicate Effect _∙_≈_
open import Core.Logic Effect _∙_≈_

open Connectives {!!} {!!}

{- Semantics for higher-order effects -}

record Elaboration (η : Effectᴴ) (ε : Effect) : Set₁ where
  constructor e⟨_⟩
  field
    elab : □ (Algebra η ∘ Free) ε

  elaborate : ∀[ Hefty η ⇒ Free ε ]
  elaborate = fold-hefty pure (□-extract elab)

instance elab-monotone : Monotone (Elaboration η)
elab-monotone .weaken i e⟨ elab ⟩ = e⟨ weaken i elab ⟩

open Elaboration public

open □
open _✴_

_⟪⊕⟫_ : ∀[ Elaboration η₁ ⇒ Elaboration η₂ ⇒ Elaboration (η₁ ⊕ η₂) ]
(e₁ ⟪⊕⟫ e₂) .elab = necessary λ i → (□⟨ e₁ .elab ⟩ i) ⟨⊕⟩ (□⟨ e₂ .elab ⟩ i)

compose-elab : ∀[ (Elaboration η₁ ✴ Elaboration η₂) ⇒ Elaboration (η₁ ⊕ η₂)  ]
compose-elab (e₁ ✴⟨ σ ⟩ e₂) = weaken (-, σ) e₁ ⟪⊕⟫ weaken (-, ∙-comm σ) e₂

extend-elab : ∀[ Elaboration η₁ ⇒ (Elaboration η₂ ─✴ Elaboration (η₁ ⊕ η₂)) ]
extend-elab = ✴-curry′ compose-elab



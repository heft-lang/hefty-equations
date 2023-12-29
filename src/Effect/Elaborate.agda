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
open import Effect.Logic as Logic

open import Function hiding (_⇔_)

open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality using (refl ; _≡_ ; subst ; sym ; trans)

open import Effect.Handle

module Effect.Elaborate where

open import Core.MonotonePredicate Effect _≲_
open Logic.Connectives

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

-- "Homogeneous" composition of elaborations. Combines two elaborations that
-- assume the *same* lower bound on the effects that they elaborate into
_⟪⊕⟫_ : ∀[ Elaboration η₁ ⇒ Elaboration η₂ ⇒ Elaboration (η₁ ⊕ η₂) ]
(e₁ ⟪⊕⟫ e₂) .elab = necessary λ i → (□⟨ e₁ .elab ⟩ i) ⟨⊕⟩ (□⟨ e₂ .elab ⟩ i)

-- "Heterogeneous" composition of elaborations. Combines two elaborations that
-- assume a *different* lower bound on the algebraic effects that they elaborate
-- into
compose-elab : ∀[ (Elaboration η₁ ✴ Elaboration η₂) ⇒ Elaboration (η₁ ⊕ η₂)  ]
compose-elab (e₁ ✴⟨ σ ⟩ e₂) = weaken (≲-∙-left σ) e₁ ⟪⊕⟫ weaken (≲-∙-right σ) e₂

-- The adjoint relation between separating conjuntion and implication gives us
-- an equivalent operation that, given an elaboration, returns an "extension
-- operation" that captures the concept of extending other elaborations with a
-- known/given elaboration. The separating implication operation deals with the
-- different lower bounds these elaborations assume on the algebraic effects
-- they elaborate into.
--
-- Or, in other words, we can curry (and thus partially apply) the heterogeneous
-- composition operation.
extend-with : ∀[ Elaboration η₁ ⇒ (Elaboration η₂ ─✴ Elaboration (η₁ ⊕ η₂)) ]
extend-with = ✴-curry compose-elab 

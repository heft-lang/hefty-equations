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

module Effect.Handle where


{- Semantics for 1st order effects -}


-- Handers of an effect are algebras over its signatures
record Handler (ε : Effect) (P : Set) (F : Set → Set) : Set₁ where
  field
    gen   : ∀[ id ⇒ const P ⇒ F ] 
    hdl   : ∀ {ε′} → Algebraᶜ ε (P → Free ε′ (F A))      

open Handler public 

fwd : {P : Set} → Algebraᶜ C (P → Free C A)
fwd .αᶜ ⟨ c , p ⟩ v = impure ⟨ c , flip p v ⟩

open Inverse
open DisjointUnion
open _∙_≈_

sift : ε₁ ∙ ε₂ ≈ ε → ∀[ Free ε ⇒ Free (ε₁ ⊕ᶜ ε₂) ]
sift _ (pure x)   = pure x
sift σ (impure ⟨ s , p ⟩) = impure (coproduct-lemma .to (σ .sep _ .union .from ⟨ s , sift σ ∘ p ⟩)) 

handle : Handler ε₁ A F → ε₁ ∙ ε₂ ≈ ε → A → ∀[ Free ε ⇒ Free ε₂ ∘ F ] 
handle H σ x t = fold-free (pure ∘₂ H .gen) (H .hdl ⟨⊕⟩ᶜ fwd) (sift σ t) x

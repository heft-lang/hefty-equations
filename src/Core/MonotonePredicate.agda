
import Relation.Unary 

open import Core.Functor 
open import Core.Ternary as Ternary

open import Function hiding (_⟨_⟩_)
open import Level
open import Data.Product

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality renaming (refl to ≡-refl ; trans to ≡-trans)


-- Definines so-called "monotone" predicates.
--
-- Another way of viewing such predicates is as functors over a category defined
-- by a preorder. In this perspective, the functorial action on morphisms
-- induces a natural notion of weakening, which naturally extends to a notion of
-- "monotonicity respecting" predicate transformers, analogous to the functor
-- instances defined in Core.Functor.
module Core.MonotonePredicate {ℓ}
  (Carrier : Set ℓ)
  (_~_ : Rel Carrier ℓ)
  (~-isPreorder : IsPreorder _≡_ _~_) where

-- Crucialy, we define monotone predicates w.r.t. the extension order (or, free
-- preorder) generated from a unital and transitive ternary relation. This
-- ensures the infrastructure in this module plays nice with the separation
-- connectives defined in Core.Logic,

open Relation.Unary    

variable P Q P₁ P₂ Q₁ Q₂ P′ Q′ : Pred Carrier ℓ

open IsPreorder ~-isPreorder 

-- Monotonicity of predicates. Or, in other words, monotone predicates are
-- functors over the (thin) category defined by the preorder _~_ (and thus
-- should respect the functor laws). 
record Monotone (P : Pred Carrier ℓ) : Set (suc ℓ) where
  field
    weaken      : ∀ {x y} → x ~ y → P x → P y 

open Monotone ⦃...⦄ public

record HMonotone (T : Pred Carrier ℓ → Pred Carrier ℓ) : Set (suc ℓ) where
  field
    ⦃ T-respects-monotonicity ⦄ : ⦃ Monotone P ⦄ → Monotone (T P)
    transform : ∀[ P ⇒ Q ] → ∀[ T P ⇒ T Q ]
    
open HMonotone ⦃...⦄ public 

-- Should also respect functor laws, but we don't really use this (yet), so TODO? 
record Antitone (P : Pred Carrier ℓ) : Set (suc ℓ) where 
  field strengthen : ∀ {x y} → x ~ y → P y → P x

open Antitone ⦃...⦄ public 

record _⊣_ (L R : Pred Carrier ℓ → Pred Carrier ℓ) ⦃ _ : HMonotone L ⦄ ⦃ _ : HMonotone R ⦄ : Set (suc ℓ) where
  field
    φ  : ⦃ Monotone P ⦄ → ⦃ Monotone Q ⦄ → ∀[ L P ⇒ Q ] → ∀[ P ⇒ R Q ]
    φᵒ : ⦃ Monotone P ⦄ → ⦃ Monotone Q ⦄ → ∀[ P ⇒ R Q ] → ∀[ L P ⇒ Q ]

    -- TODO: these should be inverses

  -- Every adjunction atomatically induces a monad/comonad pair

  M : Pred Carrier ℓ → Pred Carrier ℓ
  M = R ∘ L

  W : Pred Carrier ℓ → Pred Carrier ℓ
  W = L ∘ R

  unit : ⦃ Monotone P ⦄ → ∀[ P ⇒ M P ]
  unit = φ id

  counit : ⦃ Monotone P ⦄ → ∀[ W P ⇒ P ]
  counit = φᵒ id

  join : ⦃ Monotone P ⦄ → ∀[ M (M P) ⇒ M P ]
  join = transform counit 

  duplicate : ⦃ Monotone P ⦄ → ∀[ W P ⇒ W (W P) ]
  duplicate = transform unit

open _⊣_ public 

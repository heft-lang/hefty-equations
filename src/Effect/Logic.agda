-- Defines a modal separation logic for predicates over effects, based on the
-- ternary effect separation predicate defined in Effect.Separation 

open import Relation.Unary

open import Effect.Base
open import Effect.Separation

module Effect.Logic where

open import Level

module Connectives where

  -- Separating conjunction
  record _✴_ {ℓ} (P Q : Pred Effect ℓ) (ε : Effect) : Set (suc 0ℓ ⊔ ℓ) where 
    constructor _✴⟨_⟩_
    field
      {εₗ εᵣ} : Effect
      px  : P εₗ
      sep : εₗ ∙ εᵣ ≈ ε
      qx  : Q εᵣ  

  -- Separating implication, or, the "magic wand" 
  record _─✴_ {ℓ} (P Q : Pred Effect ℓ) (x : Effect) : Set (suc 0ℓ ⊔ ℓ) where
    constructor wand
    field
      _⟨_⟩_ : ∀ {c₁ c₂} → x ∙ c₁ ≈ c₂ → P c₁ → Q c₂
  
  open _✴_
  open _─✴_

  variable
    ℓ : Level
    P Q P₁ P₂ P′ Q₁ Q₂ Q′ : Effect → Set ℓ

  -- Separating implication is right-adjoint to separating conjunction, as
  -- witnessed by the following functions (which should be inverses)
  
  ✴-curry : ∀[ (P₁ ✴ P₂) ⇒ Q ] → ∀[ P₁ ⇒ (P₂ ─✴ Q) ]
  ✴-curry f px₁ = wand (λ σ px₂ → f (px₁ ✴⟨ σ ⟩ px₂))
                                                 
  ✴-uncurry : ∀[ P₁ ⇒ (P₂ ─✴ Q) ] → ∀[ (P₁ ✴ P₂) ⇒ Q ]
  ✴-uncurry f (px₁ ✴⟨ σ ⟩ px₂) = f px₁ ⟨ σ ⟩ px₂

  -- Some this I have yet to verify, and all of it is digression. But some
  -- remarks:
  --
  -- The currying/uncurring functions above witness that the category of
  -- monotone predicates over effects has a closed monoidal structure, with ✷ as
  -- the tensor product.
  --
  -- Later, we will see that this is not the only closed monoidal structure on
  -- this category. In fact, the "regular" (i.e., non-separating) conjunction of
  -- predicates also has a right adjoint: the Kripke function space!
  --
  -- One might wonder what sets these monoidal structures apart. Squinting a
  -- little, we can see that the definition of separating conjunction above is
  -- strikinly similar to how Day's convolution product is computed using
  -- coends. The immediate follow-up question is wether separating conjunction
  -- preserves the monoidal structure of its inputs. If so, it, together with
  -- the magic wand (whose definition, incidently, precisely mimics how the
  -- right adjoint of the Day convolution product is usually computed in terms
  -- of ends) defines a closed monoidal structure on the category of monotone
  -- *monoidal* predicates over effects. 
  

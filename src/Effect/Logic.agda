-- Defines a modal separation logic for predicates over effects, based on the
-- ternary effect separation predicate defined in Effect.Separation 

open import Relation.Unary

open import Effect.Base
open import Effect.Separation

open import Data.Product
open import Function using (_$_)
open import Level

open import Core.MonotonePredicate Effect _≲_

module Effect.Logic where

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
  
  open _✴_  public 
  open _─✴_ public 

  variable
    ℓ : Level
    --P Q P₁ P₂ P′ Q₁ Q₂ Q′ : Effect → Set ℓ

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
  

  {- Boxes and diamonds -} 
  
  
  -- The posibility modality. One way to think about posibility is as a unary
  -- version of separating conjunction. 
  record ◇ (P : Pred Effect ℓ) (x : Effect) : Set (suc 0ℓ ⊔ ℓ) where
    constructor ◇⟨_⟩_ 
    field
      {x′}    : Effect
      i       : x′ ≲ x 
      px      : P x′ 
  
  open ◇ public 
  
  -- The necessity modality. In a similar spirit, we can view necessity as a unary
  -- version of separating implication.
  record □ (P : Pred Effect ℓ) (x : Effect) : Set (suc 0ℓ ⊔ ℓ) where
    constructor necessary 
    field
      □⟨_⟩_ : ∀ {x′} → x ≲ x′ → P x′  
  
  open □ public 

  □-extract : ∀[ □ P ⇒ P ]
  □-extract px = □⟨ px ⟩ ≲-refl 

  □-duplicate : ∀[ □ P ⇒ □ (□ P ) ]
  □-duplicate px = necessary λ i → necessary (λ i′ → □⟨ px ⟩ ≲-trans i i′) 


  -- All necessities are monotone by default.
  instance □-monotone : Monotone (□ P)
  □-monotone .weaken i px = necessary λ i′ → □⟨ px ⟩ ≲-trans i i′ 

  -- Box and diamond are adjoint functors on the category of monotone predicates
  
  mod-curry : ∀[ ◇ P ⇒ Q ] → ∀[ P ⇒ □ Q ]
  mod-curry f px = necessary λ i → f $ ◇⟨ i ⟩ px
  
  mod-uncurry : ∀[ P ⇒ □ Q ] → ∀[ ◇ P ⇒ Q ]
  mod-uncurry f (◇⟨ i ⟩ px) = □⟨ f px ⟩ i
  

  -- A "Kripke closed monoidal structure" on the category of monotone predicates 
  
  -- The "Kripke exponent" (or, Kripke function space) between two predicates is
  -- defined as the necessity of their implication.
  _⇛_ : (P Q : Pred Effect ℓ) → Pred Effect (suc 0ℓ ⊔ ℓ) 
  P ⇛ Q = □ (P ⇒ Q) 
  
  kripke-curry : ⦃ Monotone P₁ ⦄ → ∀[ (P₁ ∩ P₂) ⇒ Q ] → ∀[ P₁ ⇒ (P₂ ⇛ Q) ] 
  kripke-curry f px₁ = necessary λ i px₂ → f (weaken i px₁ , px₂) 
  
  kripke-uncurry : ∀[ P₁ ⇒ (P₂ ⇛ Q) ] → ∀[ (P₁ ∩ P₂) ⇒ Q ] 
  kripke-uncurry f (px₁ , px₂) = □⟨ f px₁ ⟩ ≲-refl $ px₂
  
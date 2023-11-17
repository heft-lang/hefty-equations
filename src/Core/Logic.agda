import Relation.Unary 

open import Core.Ternary as Ternary

open import Function hiding (_⟨_⟩_)
open import Level
open import Data.Product 

module Core.Logic {ℓ} (Carrier : Set ℓ) (_∙_≈_ : Rel₃ ℓ ℓ Carrier ) where

open Relation.Unary  public   
open Ternary.Relation Carrier _∙_≈_

variable P Q P₁ P₂ Q₁ Q₂ P′ Q′ : Pred Carrier ℓ

record _⊣_ (L R : Pred Carrier ℓ → Pred Carrier ℓ) : Set (suc ℓ) where 
  field
    iso : ∀[ L P ⇒ Q ] ↔ ∀[ P ⇒ R Q ]


  module _ {P Q} where 
    open Inverse (iso {P} {Q}) 

    φ = from
    φᵒ = to

  -- Every pair of adjoint predicate transformers gives rise to a monad/comonad pair

  M : Pred Carrier ℓ → Pred Carrier ℓ
  M = R ∘ L

  W : Pred Carrier ℓ → Pred Carrier ℓ
  W = L ∘ R

  unit : ∀[ P ⇒ M P ]
  unit = φᵒ id

  counit : ∀[ W P ⇒ P ]
  counit = φ id

-- TODO : this requires additionaly that P and Q are functorial/monotone, and
-- that L and R respect this structure
-- 
--   join : ∀[ M (M P) ⇒ M P ]
--   join = {!!}
-- 
--   duplicate : ∀[ W P ⇒ W (W P) ]
--   duplicate = {!!} 


record _✴_ (P Q : Pred Carrier ℓ) (x : Carrier) : Set ℓ where 
  constructor _✴⟨_⟩_
  field
    {c₁ c₂} : Carrier
    px  : P c₁
    sep : c₁ ∙ c₂ ≈ x
    qx  : Q c₂

record _─✴_ (P Q : Pred Carrier ℓ) (x : Carrier) : Set ℓ where
  constructor wand
  field
    _⟨_⟩_ : ∀ {c₁ c₂} → x ∙ c₁ ≈ c₂ → P c₁ → Q c₂

open _✴_
open _─✴_

module _ (assocʳ : RightAssociative) where 

  ✴-curry : ∀[ (P₁ ✴ P₂) ─✴ Q ] → ∀[ P₁ ─✴ (P₂ ─✴ Q) ]
  ✴-curry f = wand
    λ σ₁ px₁ → wand
      λ σ₂ px₂ →
        f ⟨ assocʳ σ₁ σ₂ .proj₂ .proj₁
          ⟩ ( px₁ ✴⟨ assocʳ σ₁ σ₂ .proj₂ .proj₂
                   ⟩ px₂) 

module _ (assocˡ : LeftAssociative) where 

  ✴-uncurry : ∀[ P₁ ─✴ (P₂ ─✴ Q) ] → ∀[ (P₁ ✴ P₂) ─✴ Q ]
  ✴-uncurry f = wand
    λ σ ppx →
      ( f ⟨ assocˡ σ (ppx .sep) .proj₂ .proj₂
          ⟩ ppx .px
      ) ⟨ assocˡ σ (ppx .sep) .proj₂ .proj₁
        ⟩ ppx .qx




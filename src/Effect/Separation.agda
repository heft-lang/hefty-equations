open import Core.Functor
open import Core.Container

open import Effect.Base
open import Effect.Instance.Empty.Syntax

open import Relation.Unary hiding (Empty)
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])

open import Relation.Binary.PropositionalEquality.Properties renaming (isEquivalence to ≡-isEquivalence)
open import Relation.Binary.Bundles
open import Relation.Binary.Definitions

open import Function hiding (_⇔_)

open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Empty.Polymorphic

import Core.Ternary as Ternary
open import Core.DisjointUnion

open import Level

module Effect.Separation where

module U = Ternary.Relation Set DisjointUnion 

PointwiseDisjointUnion : (F G H : Set → Set) → Set _
PointwiseDisjointUnion F G H = U.Pointwise _ F G H

PointwiseInclusion : (F G : Set → Set) → Set _
PointwiseInclusion F G = Ternary.Relation.Ext _ PointwiseDisjointUnion F G

-- Container/effect separation
record _∙_≈_ (ε₁ ε₂ ε : Effect) : Set₁ where
  field
    sep : PointwiseDisjointUnion ⟦ ε₁ ⟧ᶜ ⟦ ε₂ ⟧ᶜ ⟦ ε ⟧ᶜ 

open _∙_≈_

{- transfer some properties of disjoint union to the pointwise version -} 

open Ternary.Relation {ℓ = suc 0ℓ} (Set → Set) 

punion-unitˡ : LeftIdentity PointwiseDisjointUnion λ _ → ⊥
punion-unitˡ _ = disjoint-union-unitˡ

punion-unitʳ : RightIdentity PointwiseDisjointUnion λ _ → ⊥ 
punion-unitʳ _ = disjoint-union-unitʳ

punion-comm : Commutative PointwiseDisjointUnion
punion-comm σ _ = disjoint-union-comm (σ _)

punion-assocʳ : RightAssociative PointwiseDisjointUnion
punion-assocʳ σ₁ σ₂ =
    (λ A → disjoint-union-assocʳ (σ₁ A) (σ₂ A) .proj₁)
  , (λ A → disjoint-union-assocʳ (σ₁ A) (σ₂ A) .proj₂ .proj₁)
  , (λ A → disjoint-union-assocʳ (σ₁ A) (σ₂ A) .proj₂ .proj₂)

pinc-refl : Reflexive PointwiseInclusion
pinc-refl = (λ _ → ⊥) , punion-unitʳ 

pinc-transitive : Transitive PointwiseInclusion
pinc-transitive i₁ i₂ =
    punion-assocʳ (i₁ .proj₂) (i₂ .proj₂) .proj₁
  , punion-assocʳ (i₁ .proj₂) (i₂ .proj₂) .proj₂ .proj₁ 


{- A preorder on effects, that stores the difference between the bigger and
   smaller set of effects -}

record _≲_ (ε₁ ε₂ : Effect) : Set₁ where
  field
    inc : PointwiseInclusion ⟦ ε₁ ⟧ᶜ ⟦ ε₂ ⟧ᶜ 

open _≲_

≲-refl : Reflexive _≲_
≲-refl .inc = pinc-refl 

≲-trans : Transitive _≲_
≲-trans i₁ i₂ .inc = pinc-transitive (i₁ .inc) (i₂ .inc)

≲-preorder : Preorder _ _ _
≲-preorder = record
  { Carrier    = Effect
  ; _≈_        = _≡_
  ; _∼_        = _≲_
  ; isPreorder = record
    { isEquivalence = ≡-isEquivalence
    ; reflexive     = λ where refl → ≲-refl
    ; trans         = ≲-trans
    }
  } 

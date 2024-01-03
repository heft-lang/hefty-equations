open import Core.Functor
open import Core.Container

open import Effect.Base
open import Free.Base

open import Relation.Unary hiding (Empty)
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open import Relation.Binary.PropositionalEquality.Properties renaming (isEquivalence to ≡-isEquivalence)
open import Relation.Binary.Bundles
open import Relation.Binary.Definitions

open import Function hiding (_⇔_)

open import Data.Product hiding (swap)
open import Data.Sum
open import Data.Maybe
open import Data.Empty.Polymorphic
open import Data.Sum.Properties using (swap-involutive ; swap-↔)

import Core.Ternary as Ternary
open import Core.DisjointUnion

open import Function.Construct.Symmetry
open import Function.Construct.Composition

open import Level


-- Defines a separation algebra of effects (defined as containers) based on (the
-- pointwise version of) a ternary predicate characterizing disjoint unions of
-- sets. That is, effect separation is defined on top of a chosen ternary
-- separation predicate over its extension.
--
-- TODO: the development here is specialized to ternary disjoint separation, but
-- could we generalize to any arbitrary unital, commutative and associative
-- ternary relation on sets? This would permit, for example, the kind
-- overlapping unions we also use in the OOPSLA paper, which would in theory
-- also be useful for combining elaborations that share some effects, but not
-- all. Critical question would be how (if at all) this affects reasoning about
-- higher-order effects. 
module Effect.Separation where

module U = Ternary.Relation Set DisjointUnion 

PointwiseDisjointUnion : (F G H : Set → Set) → Set _
PointwiseDisjointUnion F G H = U.Pointwise _ F G H 


PointwiseInclusion : (F G : Set → Set) → Set _
PointwiseInclusion F G = Ternary.Relation.Ext _ PointwiseDisjointUnion F G

-- Container/effect separation
record _∙_≈_ (ε₁ ε₂ ε : Effect) : Set₁ where
  field
    sep         : PointwiseDisjointUnion ⟦ ε₁ ⟧ᶜ ⟦ ε₂ ⟧ᶜ ⟦ ε ⟧ᶜ 
    natural-iso : NaturalIsomorphism (DisjointUnion.union ∘ sep)  

open _∙_≈_ public 

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

swap-↔-natiso : ∀ {F G : Set → Set}
                → ⦃ _ : Functor F ⦄ → ⦃ _ : Functor G ⦄
                → NaturalIsomorphism {F = F ∪ G} {G = G ∪ F} λ _ → swap-↔
swap-↔-natiso = record
  { to-natural   = record
    { commute = [ (λ _ → refl) , (λ _ → refl) ]
    }
  ; from-natural = record
    { commute = [ (λ _ → refl) , (λ _ → refl) ]
    }
  } 

∙-comm : Ternary.Relation.Commutative Effect _∙_≈_
∙-comm σ .sep         = punion-comm (σ .sep)
∙-comm {c₁} {c₂} {c} σ .natural-iso =
  natiso-∘ {F = ⟦ c₂ ⟧ᶜ ∪ ⟦ c₁ ⟧ᶜ} {G = ⟦ c₁ ⟧ᶜ ∪ ⟦ c₂ ⟧ᶜ} {H = ⟦ c ⟧ᶜ}
    {F↔G = λ x → swap-↔}
    {G↔H = λ x → σ .sep x .DisjointUnion.union}
    swap-↔-natiso (σ .natural-iso)


{- A preorder on effects, that stores the difference between the bigger and
   smaller set of effects -}

record _≲_ (ε₁ ε₂ : Effect) : Set₁ where
  field
    inc : PointwiseInclusion ⟦ ε₁ ⟧ᶜ ⟦ ε₂ ⟧ᶜ 

open _≲_ ⦃...⦄

instance ≲-refl : Reflexive _≲_
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

inject : ⦃ ε₁ ≲ ε₂ ⦄ → Algebraᶜ ε₁ (Free ε₂ A) 
inject .αᶜ = impure ∘ inc .proj₂ _ .DisjointUnion.union .Inverse.to ∘ inj₁  

-- Effect weakening / masking for the free monad
--
-- Viewing containers as a category (with injections as morphisms), this defines
-- the action on morphisms of the Functor Free ∈ [Container,[Set,Set]]
♯ : ⦃ ε₁ ≲ ε₂ ⦄ → ∀[ Free ε₁ ⇒ Free ε₂ ]
♯ = fold-free pure inject

open Ternary

coproduct-lemma : Π[ (⟦ ε₁ ⟧ᶜ ∪ ⟦ ε₂ ⟧ᶜ) ⇔ ⟦ ε₁ ⊕ᶜ ε₂ ⟧ᶜ ]
coproduct-lemma _ = record
  { to        =
    [ (λ where ⟨ s , p ⟩ → ⟨ inj₁ s , p ⟩)
    , (λ where ⟨ s , p ⟩ → ⟨ inj₂ s , p ⟩)
    ]
  ; from      = λ where
    ⟨ inj₁ s , p ⟩ → inj₁ ⟨ s , p ⟩
    ⟨ inj₂ s , p ⟩ → inj₂ ⟨ s , p ⟩
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = ( λ where
                    ⟨ inj₁ s , p ⟩ → refl
                    ⟨ inj₂ s , p ⟩ → refl
                ) , [ (λ _ → refl) , (λ _ → refl) ]
  }

coproduct-lemma-natiso : ∀ {ε₁ ε₂} → NaturalIsomorphism $ coproduct-lemma {ε₁ = ε₁} {ε₂}
coproduct-lemma-natiso = record
  { to-natural   = λ where .commute → [ (λ _ → refl) , (λ _ → refl) ]
  ; from-natural = λ where .commute ⟨ inj₁ _ , _ ⟩ → refl
                           .commute ⟨ inj₂ _ , _ ⟩ → refl 
  } 

⊎-sym : (A ⊎ B) ↔ (B ⊎ A)
⊎-sym = record
  { to        = swap
  ; from      = swap
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = swap-involutive , swap-involutive
  }

∙-to-≋ : ε₁ ∙ ε₂ ≈ ε → (ε₁ ⊕ᶜ ε₂) ≋ ε
∙-to-≋ σ = record
  { iso         = λ x → ↔-sym (coproduct-lemma x) ↔-∘ σ .sep x .DisjointUnion.union
  ; iso-natural = natiso-∘ (natiso-sym coproduct-lemma-natiso) (σ .natural-iso)
  }

{- TODO: effect separation also respects effect equivalence in all positions. Do
we need this? -}

≲-⊕ᶜ-left : ∀ ε′ → ε ≲ (ε ⊕ᶜ ε′)
≲-⊕ᶜ-left ε′ .inc = ⟦ ε′ ⟧ᶜ , λ where _ .DisjointUnion.union → coproduct-lemma _

≲-⊕ᶜ-right : ∀ ε′ → ε ≲ (ε′ ⊕ᶜ ε)
≲-⊕ᶜ-right ε′ .inc = ⟦ ε′ ⟧ᶜ , λ where _ .DisjointUnion.union → ⊎-sym ↔-∘ (coproduct-lemma _)

≲-∙-left : ε₁ ∙ ε₂ ≈ ε → ε₁ ≲ ε
≲-∙-left σ .inc = -, σ .sep

≲-∙-right : ε₁ ∙ ε₂ ≈ ε → ε₂ ≲ ε
≲-∙-right σ .inc = -, ∙-comm σ .sep 

♯ˡ : ∀ ε₂ → ∀[ Free ε₁ ⇒ Free (ε₁ ⊕ᶜ ε₂) ]
♯ˡ ε₂ = ♯ ⦃ ≲-⊕ᶜ-left ε₂ ⦄

♯ʳ : ∀ ε₁ → ∀[ Free ε₂ ⇒ Free (ε₁ ⊕ᶜ ε₂) ]
♯ʳ ε₁ = ♯ ⦃ ≲-⊕ᶜ-right ε₁ ⦄

♯ˡ′ : (σ : ε₁ ∙ ε₂ ≈ ε) → ∀[ Free ε₁ ⇒ Free ε ]
♯ˡ′ σ = ♯ ⦃ ≲-∙-left σ ⦄

♯ʳ′ : (σ : ε₁ ∙ ε₂ ≈ ε) → ∀[ Free ε₂ ⇒ Free ε ]
♯ʳ′ σ = ♯ ⦃ ≲-∙-right σ ⦄

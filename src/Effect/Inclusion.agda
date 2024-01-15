open import Data.Product 

open import Core.Functor 
open import Core.Container
open import Core.Ternary 

open import Effect.Base 
open import Free.Base 
open import Effect.DisjointUnion

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

open import Function
open import Level

module Effect.Inclusion where

module R₃ = Relation Effect Union
open Union
open Inverse 

_≲_ : Rel Effect (suc 0ℓ)
_≲_ = R₃.Ext

inj : ⦃ ε₁ ≲ ε₂ ⦄ → ε₁ ↦ ε₂
inj ⦃ ε′ , u ⦄ = u .union _ .to ∘ injˡ ε′ 

inject : ⦃ ε₁ ≲ ε₂ ⦄ → Algebraᶜ ε₁ (Free ε₂ A)
inject .αᶜ = impure ∘ inj

♯ : ⦃ ε₁ ≲ ε₂ ⦄ → ∀[ Free ε₁ ⇒ Free ε₂ ]
♯ = fold-free pure inject

≲-refl : Reflexive _≲_
≲-refl = R₃.Ext-reflexive (⊥ᶜ , union-unitʳ)

≲-trans : Transitive _≲_
≲-trans = R₃.Ext-transitive union-assocʳ

≲-isPreorder : IsPreorder _≡_ _≲_
≲-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = λ where refl → ≲-refl
  ; trans         = ≲-trans
  } 

≲-preorder : Preorder _ _ _
≲-preorder = record
  { Carrier    = Effect
  ; _≈_        = _≡_
  ; _∼_        = _≲_
  ; isPreorder = ≲-isPreorder
  }


 

{-# OPTIONS --without-K #-} 

open import Relation.Unary

open import Core.Functor
open import Core.Container
open import Core.Signature

open import Effect.Syntax.Free
open import Effect.Syntax.Hefty

open import Data.Empty 
open import Data.Product
open import Data.Sum

open import Function hiding (_⇔_)
open import Function.Construct.Identity using (↔-id)
open import Function.Construct.Symmetry using (↔-sym)
open import Function.Construct.Composition using (_↔-∘_)

open import Relation.Binary using (Preorder)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality using (refl ; _≡_ ; subst ; sym ; trans)

module Effect.Base where

Effect  = Container 
Effectᴴ = Signature

↑ : Effect → Effectᴴ
↑ ε = record
  { command  = ε .shape
  ; response = ε .position
  ; fork     = λ _ → ⊥ 
  ; returns  = λ()
  }

variable ε ε₁ ε₂ ε₃ ε′ : Effect
         η η₁ η₂ η₃ η′ : Effectᴴ
         ξ ξ₁ ξ₂ ξ₃ ξ′    : Effect → Effectᴴ 

embed : ∀[ F ⊢ ⟦ ε ⟧ᶜ ⇒ ⟦ ↑ ε ⟧ F ]
embed ⟨ s , p ⟩ .reflect = s , p , λ()

embed-free : ∀[ Free ε ⇒ Hefty (↑ ε) ]
embed-free = fold-free pure λ where .αᶜ x → impure (embed x)

-- Signature/highe-order effect morphisms

record _⊑ᴴ_ (η₁ η₂ : Effectᴴ) : Set₁ where
  field
  
    injᴴ-c          : η₁ .command → η₂ .command
    
    response-stable : ∀ {c}
                      → η₁ .response c ≡ η₂ .response (injᴴ-c c)
                      
    fork-stable     : ∀ {c}
                      → η₁ .fork c ≡ η₂ .fork (injᴴ-c c)
                      
    types-stable    : ∀ {c} {ψ : η₂ .fork (injᴴ-c c)}
                      → η₁ .returns (subst id (sym fork-stable) ψ) ≡ η₂ .returns ψ

  injᴴ : ⦃ Functor F ⦄ → ∀[ ⟦ η₁ ⟧ F ⇒ ⟦ η₂ ⟧ F ]
  injᴴ ⟪ c , r , s ⟫ =
    ⟪ (injᴴ-c c
    , r ∘ subst id (sym response-stable)
    , fmap (subst id types-stable) ∘ s ∘ subst id (sym fork-stable))
    ⟫

open _⊑ᴴ_ ⦃...⦄ public 

free-resp-⇿ : ε₁ ⇿ ε₂ → ∀[ Free ε₁ ⇒ Free ε₂ ]
free-resp-⇿ eq = hmap-free (eq .equivalence _ .Inverse.to) 

injectᴴ : ⦃ η₁ ⊑ᴴ η₂ ⦄ → Algebra η₁ (Hefty η₂)
injectᴴ .α v = impure (injᴴ v)  

♯ᴴ : ⦃ η₁ ⊑ᴴ η₂ ⦄ → ∀[ Hefty η₁ ⇒ Hefty η₂ ]
♯ᴴ = fold-hefty {F = Hefty _} pure injectᴴ

⊑ᴴ-refl : η ⊑ᴴ η
⊑ᴴ-refl = record
  { injᴴ-c          = id
  ; response-stable = refl
  ; fork-stable     = refl
  ; types-stable    = refl
  }  

postulate TODO : ∀ {a} {A : Set a} → A 

⊑ᴴ-trans : η₁ ⊑ᴴ η₂ → η₂ ⊑ᴴ η₃ → η₁ ⊑ᴴ η₃
⊑ᴴ-trans sub₁ sub₂ = record
  { injᴴ-c          = injᴴ-c ⦃ sub₂ ⦄ ∘ injᴴ-c ⦃ sub₁ ⦄
  ; response-stable = trans (response-stable ⦃ sub₁ ⦄) (response-stable ⦃ sub₂ ⦄)
  ; fork-stable     = trans (fork-stable ⦃ sub₁ ⦄) (fork-stable ⦃ sub₂ ⦄)
  ; types-stable    = trans TODO (types-stable ⦃ sub₂ ⦄)
  }

⊑ᴴ-⊕-left : η₁ ⊑ᴴ (η₁ ⊕ η₂)
⊑ᴴ-⊕-left = record
  { injᴴ-c          = inj₁
  ; response-stable = refl
  ; fork-stable     = refl
  ; types-stable    = refl
  } 

⊑ᴴ-⊕-right : η₂ ⊑ᴴ (η₁ ⊕ η₂)
⊑ᴴ-⊕-right = record
  { injᴴ-c          = inj₂
  ; response-stable = refl
  ; fork-stable     = refl
  ; types-stable    = refl
  }
  


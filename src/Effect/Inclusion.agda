{-# OPTIONS --without-K #-} 

open import Data.Product 

open import Core.Functor 
open import Core.Functor.NaturalTransformation
open import Core.Functor.Monad

open import Core.Container
open import Core.Ternary 
open import Core.Extensionality

open import Effect.Base 
open import Effect.Syntax.Free 
open import Effect.Separation

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

open import Data.Sum 
open import Data.Product

open import Function
open import Level

module Effect.Inclusion where

module R₃ = Relation Effect Union
open Union
open Inverse 

_≲_ : Rel Effect (suc 0ℓ)
_≲_ = R₃.Ext

≲-refl = R₃.Ext-reflexive (⊥ᶜ , union-unitʳ)
≲-trans = R₃.Ext-transitive union-assocʳ

≲-preorder : Preorder _ _ _
≲-preorder = R₃.Ext-preorder (⊥ᶜ , union-unitʳ) union-assocʳ 

-- some properties about effect inclusion 
module _ where

 ≲-⊕ᶜ-left : ∀ ε′ → ε ≲ (ε ⊕ᶜ ε′)
 ≲-⊕ᶜ-left ε′ = ε′ , ⊕ᶜ-union 
  
 ≲-⊕ᶜ-right : ∀ ε′ → ε ≲ (ε′ ⊕ᶜ ε)
 ≲-⊕ᶜ-right {ε} ε′ = ε′ , union-respects-⇿ .R₃.r₃ (swapᶜ-⇿ ε ε′) ⊕ᶜ-union

 ≲-∙-left : ε₁ ∙ ε₂ ≈ ε → ε₁ ≲ ε
 ≲-∙-left σ = _ , σ 

 ≲-∙-right : ε₁ ∙ ε₂ ≈ ε → ε₂ ≲ ε
 ≲-∙-right σ = _ , union-comm σ

 ≲-respects-⇿ˡ : ε₁ ⇿ ε₂ → ε₁ ≲ ε → ε₂ ≲ ε
 ≲-respects-⇿ˡ eq (ε′ , σ) = ε′ , union-respects-⇿ .R₃.r₁ eq σ

 ≲-respects-⇿ʳ : ε₁ ⇿ ε₂ → ε ≲ ε₁ → ε ≲ ε₂
 ≲-respects-⇿ʳ eq (ε′ , σ) = ε′ , union-respects-⇿ .R₃.r₃ eq σ 

-- Transforming an effect tree's signature using inclusions and separations
module _ where

  inj : ⦃ ε₁ ≲ ε₂ ⦄ → ε₁ ↦ ε₂
  inj ⦃ ε′ , u ⦄ = u .union .equivalence _ .to ∘ injˡ ε′ 

  inj-natural : ⦃ i : ε₁ ≲ ε₂ ⦄ → Natural inj
  inj-natural ⦃ i ⦄ .commute {f = f} ⟨ c , k ⟩ = i .proj₂ .union .natural .to-natural .commute {f = f} _
    
  inject : ⦃ ε₁ ≲ ε₂ ⦄ → Algebraᶜ ε₁ (Free ε₂ A)
  inject .αᶜ = impure ∘ inj

  ♯ : ⦃ ε₁ ≲ ε₂ ⦄ → ∀[ Free ε₁ ⇒ Free ε₂ ]
  ♯ = hmap-free inj
  
  ♯ˡ : ∀ ε₂ → ∀[ Free ε₁ ⇒ Free (ε₁ ⊕ᶜ ε₂) ]
  ♯ˡ ε₂ = ♯ ⦃ ≲-⊕ᶜ-left ε₂ ⦄

  ♯ʳ : ∀ ε₁ → ∀[ Free ε₂ ⇒ Free (ε₁ ⊕ᶜ ε₂) ]
  ♯ʳ ε₁ = ♯ ⦃ ≲-⊕ᶜ-right ε₁ ⦄

  ♯ˡ′ : (σ : ε₁ ∙ ε₂ ≈ ε) → ∀[ Free ε₁ ⇒ Free ε ]
  ♯ˡ′ σ = ♯ ⦃ ≲-∙-left σ ⦄

  ♯ʳ′ : (σ : ε₁ ∙ ε₂ ≈ ε) → ∀[ Free ε₂ ⇒ Free ε ]
  ♯ʳ′ σ = ♯ ⦃ ≲-∙-right σ ⦄


-- Properties of weakening
module _ where 

  -- Weakenings respect identities
  ♯-id :
    ∀ ⦃ i : ε ≲ ε′ ⦄
    → (x : A)
      -------------------
    → ♯ (pure x) ≡ pure x
  ♯-id x = refl

  -- Weakenings are natural transformations 
  ♯-natural : ⦃ _ : ε ≲ ε′ ⦄ → Natural ♯
  ♯-natural = hmap-natural inj inj-natural 

  -- Weakening respects monadic bind 
  ♯-coherent :
    ∀ ⦃ i : ε ≲ ε′ ⦄
    → (m : Free ε A)
    → (k : A → Free ε B)
      ---------------------------------
    → ♯ (m >>= k) ≡ ♯ ⦃ i ⦄ m >>= ♯ ∘ k
  ♯-coherent (pure x)             k = refl
  ♯-coherent (impure ⟨ c , k′ ⟩ ) k =
    begin
      ♯ (impure ⟨ c , k′ ⟩ >>= k)
    ≡⟨⟩ 
      ♯ (impure ⟨ c , k′ >=> k ⟩)
    ≡⟨⟩ 
      impure (inj ⟨ c , ♯ ∘ (k′ >=> k) ⟩)
    ≡⟨ cong (λ ○ → impure (inj ⟨ (c , ○) ⟩)) (extensionality λ x → ♯-coherent (k′ x) k) ⟩
      impure (inj ⟨ c , (λ x → ♯ (k′ x) >>= ♯ ∘ k) ⟩)
    ≡⟨ cong impure (inj-natural .commute {f = _>>= ♯ ∘ k} ⟨ (c , ♯ ∘ k′) ⟩) ⟩
      impure (fmap {F = ⟦ _ ⟧ᶜ } (_>>= (♯ ∘ k)) (inj ⟨ c , ♯ ∘ k′ ⟩))
    ≡⟨⟩
      ♯ (impure ⟨ c , k′ ⟩) >>= ♯ ∘ k
    ∎
    where open ≡-Reasoning 

  -- Weakening is a monad morphism
  --
  -- Or, another perspective is to say that weakening defines a functor between
  -- the category of containers and the category of monad morhpisms, that sends
  -- containers to their respective free monad, and container morphisms to
  -- weakenings
  ♯-mm : ⦃ ε ≲ ε′ ⦄ → MonadMorphism (Free ε) (Free ε′)
  ♯-mm = record
    { Ψ         = ♯
    ; Ψ-natural = ♯-natural
    ; resp-unit = extensionality ♯-id
    ; resp-join = λ f g → extensionality λ x → ♯-coherent (f x) g
    } 

-- (Extensional) equivalence of inclusion witnesses 
module _ where

  record _⇔≲_ {ε₁ ε₂} (i₁ i₂ : ε₁ ≲ ε₂) : Set₁ where
    field
      ≗-inj   : ∀ {X : Set} {x : ⟦ _ ⟧ᶜ X} → inj ⦃ i₁ ⦄ x ≡ inj ⦃ i₂ ⦄ x

  open _⇔≲_


  -- witness equivalence is indeed in equivalence relation

  ⇔≲-refl : (i : ε₁ ≲ ε₂) → i ⇔≲ i
  ⇔≲-refl i = record { ≗-inj = refl }

  ⇔≲-sym  : (i₁ i₂ : ε₁ ≲ ε₂) → i₁ ⇔≲ i₂ → i₂ ⇔≲ i₁
  ⇔≲-sym i₁ i₂ eq = record { ≗-inj = sym (eq .≗-inj) }

  ⇔≲-trans : (i₁ i₂ i₃ : ε₁ ≲ ε₂) → i₁ ⇔≲ i₂ → i₂ ⇔≲ i₃ → i₁ ⇔≲ i₃
  ⇔≲-trans i₁ i₂ i₃ eq₁ eq₂ = record { ≗-inj = trans (eq₁ .≗-inj) (eq₂ .≗-inj) }



  -- inclusion witnesses form a monoid w.r.t. the equivalence relation defined above

  ⇔≲-identityˡ : (i : ε₁ ≲ ε) → ≲-trans ≲-refl i ⇔≲ i
  ⇔≲-identityˡ i = record { ≗-inj = refl }

  ⇔≲-identityʳ : (i : ε₁ ≲ ε₂) → ≲-trans i ≲-refl ⇔≲ i
  ⇔≲-identityʳ i = record { ≗-inj = refl } 

  ⇔≲-assoc : (i₁ : ε₁ ≲ ε₂) (i₂ : ε₂ ≲ ε₃) (i₃ : ε₃ ≲ ε) → ≲-trans (≲-trans i₁ i₂) i₃ ⇔≲ ≲-trans i₁ (≲-trans i₂ i₃)   
  ⇔≲-assoc i₁ i₂ i₃ = record { ≗-inj = refl }
  
  ⇔≲-trans-congₗ : (i₁ i₂ : ε₁ ≲ ε₂) (i : ε₂ ≲ ε′) → i₁ ⇔≲ i₂ → ≲-trans i₁ i ⇔≲ ≲-trans i₂ i 
  ⇔≲-trans-congₗ i₁ i₂ i eq = record { ≗-inj = cong (λ x → inj ⦃ i ⦄ x) (eq .≗-inj) }

  ⇔≲-trans-congᵣ : (i : ε′ ≲ ε₁) (i₁ i₂ : ε₁ ≲ ε₂) → i₁ ⇔≲ i₂ → ≲-trans i i₁ ⇔≲ ≲-trans i i₂ 
  ⇔≲-trans-congᵣ i i₁ i₂ eq = record { ≗-inj = eq .≗-inj }

  ⇔≲-resp-⇿ˡ : (i₁ i₂ : ε₁ ≲ ε′) (eq : ε₁ ⇿ ε₂) → i₁ ⇔≲ i₂ → ≲-respects-⇿ˡ eq i₁ ⇔≲ ≲-respects-⇿ˡ eq i₂ 
  ⇔≲-resp-⇿ˡ i₁ i₂ eq eq′ = record { ≗-inj = eq′ .≗-inj }

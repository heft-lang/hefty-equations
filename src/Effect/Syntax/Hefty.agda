{-# OPTIONS --without-K #-} 

open import Relation.Unary
open import Function
open import Data.Product 

open import Core.Functor
open import Core.Signature
open import Core.Extensionality

open import Relation.Binary.PropositionalEquality using (refl ; _≡_ ; subst ; sym ; trans ; cong)

module Effect.Syntax.Hefty where

data Hefty (σ : Signature) (A : Set) : Set where
  pure   : A                  → Hefty σ A 
  impure : ⟦ σ ⟧ (Hefty σ) A  → Hefty σ A

variable m m₁ m₂ m₃ m′ : Hefty σ A 

instance hefty-pointed : Pointed (Hefty σ)
hefty-pointed = record
  { point = pure
  } 

fold-hefty : ∀[ id ⇒ F ] → Algebra σ F → ∀[ Hefty σ ⇒ F ]
fold-hefty η y (pure x)                = η x
fold-hefty η y (impure ⟪ c , r , s ⟫ ) = y .α ⟪ c , fold-hefty η y ∘ r , fold-hefty η y ∘ s ⟫ 

rec-hefty : ⦃ Pointed F ⦄ → (A → F B) → Algebra σ F → Hefty σ A → F B
rec-hefty k _ (pure x)               = k x
rec-hefty k y (impure ⟪ c , r , s ⟫) = y .α ⟪ c , rec-hefty k y ∘ r , rec-hefty point y ∘ s ⟫

map-hefty : (A → B) → Hefty σ A → Hefty σ B
map-hefty f (pure x) = pure (f x)
map-hefty f (impure ⟪ c , r , s ⟫) = impure ⟪ c , map-hefty f ∘ r , s ⟫

map-hefty-id : (t : Hefty σ A) → map-hefty id t ≡ t 
map-hefty-id (pure _)               = refl
map-hefty-id (impure ⟪ c , r , s ⟫) =
  cong (λ ○ → impure ⟪ c , ○ , s ⟫)
    (extensionality (map-hefty-id ∘ r ))

map-hefty-∘ :
  ∀ {C : Set} → (f : A → B) (g : B → C) (t : Hefty σ A)
  → map-hefty g (map-hefty f t) ≡ map-hefty (g ∘ f) t
map-hefty-∘ f g (pure _)              = refl
map-hefty-∘ f g (impure ⟪ c , r , s ⟫) =
  cong (λ ○ → impure ⟪ c , ○ , s ⟫)
    (extensionality (map-hefty-∘ f g ∘ r))

bind-hefty : Hefty σ A → (A → Hefty σ B) → Hefty σ B
bind-hefty t k = rec-hefty k (λ where .α → impure) t

instance
  hefty-functor : Functor (Hefty σ)
  hefty-functor = record
    { fmap    = map-hefty
    ; fmap-id = map-hefty-id
    ; fmap-∘  = map-hefty-∘
    }


  hefty-monad : Monad (Hefty σ)
  hefty-monad = record
    { return    = point
    ; _∗        = flip bind-hefty
    ; >>=-idˡ   = λ _ _ → refl
    ; >>=-idʳ   = right-identity
    ; >>=-assoc = assoc 
    }
    where 
      open import Relation.Binary.PropositionalEquality

      right-identity : (m : Hefty σ A) → flip bind-hefty pure m ≡ m
      right-identity {σ} {A} (pure x)               = refl
      right-identity {σ} {A} (impure ⟪ c , r , s ⟫) = 
        cong₂ (λ ○₁ ○₂ → impure ⟪ c , ○₁ , ○₂ ⟫)
          (extensionality $ right-identity ∘ r)
          (extensionality $ right-identity ∘ s) 
 
      assoc : {A B D : Set} (k₁ : A → Hefty σ B) (k₂ : B → Hefty σ D) (m : Hefty σ A)
            → flip (λ y x → bind-hefty x y) (flip (λ y x → bind-hefty x y) m k₁) k₂
            ≡ flip (λ y x → bind-hefty x y) m (λ x → flip (λ y x₁ → bind-hefty x₁ y) (k₁ x) k₂)
      assoc k₁ k₂ (pure x) = refl
      assoc k₁ k₂ (impure ⟪ c , r , s ⟫) =
        cong₂ (λ ○₁ ○₂ → impure ⟪ c , ○₁ , ○₂ ⟫)
          (extensionality $ assoc k₁ k₂ ∘ r)
          (extensionality $ assoc pure pure ∘ s)

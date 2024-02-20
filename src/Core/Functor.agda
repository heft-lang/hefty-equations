{-# OPTIONS --safe --without-K #-} 

module Core.Functor where

open import Relation.Unary
open import Level renaming (suc to sℓ) 
open import Relation.Binary.PropositionalEquality

open import Data.Sum
open import Data.Product 

open import Function
open import Function.Construct.Identity
open import Function.Construct.Symmetry
open import Function.Construct.Composition

-- Lawful functors on Set, at any level 
record Functor {a b} (F : Set a → Set b) : Set (sℓ a ⊔ b) where  
  field
    fmap : {A B : Set a} → (A → B) → F A → F B

    -- Functor laws 
    fmap-id : ∀ {A : Set a} → ∀ (x : F A) → fmap id x ≡ x
    fmap-∘  :
      ∀ {A B C : Set a}
      → (f : A → B) (g : B → C)
      → (x : F A)
      → fmap g (fmap f x) ≡ fmap (g ∘ f) x 

open Functor ⦃...⦄ public

instance
  sum-functor : ∀ {a b} {F G : Set a → Set b} → ⦃ Functor F ⦄ → ⦃ Functor G ⦄ →  Functor (F ∪ G)
  Functor.fmap sum-functor f (inj₁ x) = inj₁ (fmap f x)
  Functor.fmap sum-functor f (inj₂ y) = inj₂ (fmap f y)
  Functor.fmap-id sum-functor (inj₁ x) = cong inj₁ (fmap-id x)
  Functor.fmap-id sum-functor (inj₂ y) = cong inj₂ (fmap-id y)
  Functor.fmap-∘ sum-functor f g (inj₁ x) = cong inj₁ (fmap-∘ f g x)
  Functor.fmap-∘ sum-functor f g (inj₂ y) = cong inj₂ (fmap-∘ f g y)

  id-functor : ∀ {a} → Functor {a} {a} λ x → x
  id-functor = record
    { fmap    = id
    ; fmap-id = λ x → refl
    ; fmap-∘  = λ f g x → refl
    }

-- 
--   product-functor : ∀ {a b} {F G : Set a → Set b} → ⦃ Functor F ⦄ → ⦃ Functor G ⦄ →  Functor (F ∩ G)
--   product-functor = {!!}
--


variable a b : Level
         A : Set a
         B : Set b
         F G : Set a → Set b

-- Pointed endofunctors on Set 
record Pointed (F : Set → Set) : Set₁ where
  field
    point : ∀[ id ⇒ F ]

open Pointed ⦃...⦄ public

instance  
  id-pointed : Pointed λ x → x
  id-pointed = record { point = id } 

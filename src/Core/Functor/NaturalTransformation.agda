{-# OPTIONS --safe --without-K #-} 

open import Core.Functor

open import Relation.Unary
open import Relation.Binary.PropositionalEquality 

open import Function
open import Function.Construct.Identity
open import Function.Construct.Symmetry
open import Function.Construct.Composition

open import Level renaming (suc to sℓ)

module Core.Functor.NaturalTransformation where

-- Natural transformations between functors on Set 
record Natural {a b} {F G : Set a → Set b}
               ⦃ _ : Functor F ⦄ ⦃ _ : Functor G ⦄
               (θ : ∀[ F ⇒ G ]) : Set (sℓ a ⊔ b) where
  field
    commute : ∀ {X Y} {f : X → Y} → (x : F X) → θ (fmap f x) ≡ fmap f (θ x) 

open Natural public

id-natural : ∀ {a b} {F : Set a → Set b} → ⦃ _ : Functor F ⦄ → Natural {F = F} id
id-natural = record { commute = λ _ → refl }

-- Naturality is preserved by composition
∘-natural :
  ∀ {a b} {F G H : Set a → Set b}
  → ⦃ _ : Functor F ⦄ → ⦃ _ : Functor G ⦄ → ⦃ _ : Functor H ⦄
  → (θ₁ : ∀[ F ⇒ G ]) (θ₂ : ∀[ G ⇒ H ])
  → Natural θ₁ → Natural θ₂
    -----------------------
  → Natural (θ₂ ∘ θ₁)
∘-natural θ₁ θ₂ n₁ n₂ = record
  { commute = λ _ →
      trans (cong (fmap θ₂) (n₁ .commute _)) $ n₂ .commute _
  }

record NaturalIsomorphism {a b} {F G : Set a → Set b}
                          ⦃ _ : Functor F ⦄ ⦃ _ : Functor G ⦄
                          (iso : ∀ x → F x ↔ G x) : Set (sℓ a ⊔ b) where
  field
    to-natural    : Natural (iso _ .Inverse.to)
    from-natural  : Natural (iso _ .Inverse.from) 

open NaturalIsomorphism public 


natiso-id : ∀ {a} → NaturalIsomorphism {a} ↔-id
natiso-id = record
  { to-natural   = λ where .commute _ → refl
  ; from-natural = λ where .commute _ → refl
  } 

natiso-sym : ∀ {a b} {F G : Set a → Set b}
               {F↔G : ∀ x → F x ↔ G x}
             → ⦃ _ : Functor F ⦄ → ⦃ _ : Functor G ⦄
             → NaturalIsomorphism F↔G
             → NaturalIsomorphism (↔-sym ∘ F↔G) 
natiso-sym {F = F} {G} {F↔G} natiso = record
  { to-natural   = natiso .from-natural
  ; from-natural = natiso .to-natural
  }

natiso-∘ : ∀ {a b} {F G H : Set a → Set b}
          {F↔G : ∀ x → F x ↔ G x} {G↔H : ∀ x → G x ↔ H x}
        → ⦃ _ : Functor F ⦄ → ⦃ _ : Functor G ⦄ → ⦃ _ : Functor H ⦄ 
        → NaturalIsomorphism F↔G → NaturalIsomorphism G↔H
        → NaturalIsomorphism λ x → F↔G x ↔-∘ G↔H x 
natiso-∘ {F = F} {G} {H} {F↔G} {G↔H} natiso₁ natiso₂ = record
  { to-natural   = λ where .commute → to-nat
  ; from-natural = λ where .commute → from-nat
  }
  where
    open Inverse
    open ≡-Reasoning 

    to-nat   : ∀ {X Y f} (x : F X) → (F↔G Y ↔-∘ G↔H Y) .to (fmap f x) ≡ fmap f ((F↔G X ↔-∘ G↔H X) .to x)
    to-nat {X}{Y}{f} x = begin
        (F↔G Y ↔-∘ G↔H Y) .to (fmap f x)
      ≡⟨⟩ {- Definition of ↔-∘ -} 
        G↔H Y .to (F↔G Y .to (fmap f x)) 
      ≡⟨ cong (G↔H Y .to) (natiso₁ .to-natural .commute x) ⟩
        G↔H Y .to (fmap f (F↔G X .to x))
      ≡⟨ natiso₂ .to-natural .commute _ ⟩ 
        fmap f (G↔H X .to (F↔G X .to x))
      ≡⟨⟩ {- Defintion of ↔-∘ -} 
        fmap f ((F↔G X ↔-∘ G↔H X) .to x) 
      ∎
    
    from-nat : ∀ {X Y f} (x : H X) → (F↔G Y ↔-∘ G↔H Y) .from (fmap f x) ≡ fmap f ((F↔G X ↔-∘ G↔H X) .from x)
    from-nat {X}{Y}{f} x = begin
        (F↔G Y ↔-∘ G↔H Y) .from (fmap f x)
      ≡⟨⟩ {- Definition of ↔-∘ -}
        F↔G Y .from (G↔H Y .from (fmap f x)) 
      ≡⟨ cong (F↔G Y .from) (natiso₂ .from-natural .commute x) ⟩
        F↔G Y .from (fmap f (G↔H X .from x))
      ≡⟨ natiso₁ .from-natural .commute _ ⟩
        fmap f (F↔G X .from (G↔H X .from x))
      ≡⟨⟩ {- Definition of ↔-∘ -} 
        fmap f ((F↔G X ↔-∘ G↔H X) .from x)
      ∎ 

open import Data.Product
open import Data.Sum
open import Data.Empty

open import Function
open import Relation.Unary

open import Core.Functor

open import Relation.Binary.PropositionalEquality hiding ([_])

module Core.Container where

record Container : Set₁ where
  no-eta-equality
  field shape    : Set
        position : shape → Set

  infix 1 ⟨_⟩ 
  record ⟦_⟧ᶜ (A : Set) : Set where
    constructor ⟨_⟩
    field reflectᶜ : Σ shape λ s → position s → A

  open ⟦_⟧ᶜ public

  record Algebraᶜ (A : Set) : Set where
    field αᶜ : ⟦_⟧ᶜ A → A

  open Algebraᶜ public 

open Container public

variable C C₁ C₂ C₃ : Container

_⊕ᶜ_ : (C₁ C₂ : Container) → Container
C₁ ⊕ᶜ C₂ = record
  { shape    = C₁ .shape ⊎ C₂ .shape
  ; position = [ C₁ .position , C₂ .position ]
  }

_⟨⊕⟩ᶜ_ : ∀[ Algebraᶜ C₁ ⇒ Algebraᶜ C₂ ⇒ Algebraᶜ (C₁ ⊕ᶜ C₂) ] 
(x ⟨⊕⟩ᶜ y) .αᶜ ⟨ inj₁ s , p ⟩ = x .αᶜ ⟨ s , p ⟩
(x ⟨⊕⟩ᶜ y) .αᶜ ⟨ inj₂ s , p ⟩ = y .αᶜ ⟨ s , p ⟩

-- Container morphisms are natural transformations between the extension functors 
_↦_ : Container → Container → Set₁
C₁ ↦ C₂ = ∀[ ⟦ C₁ ⟧ᶜ ⇒ ⟦ C₂ ⟧ᶜ ]

-- container isomorphism
--
-- TODO: require naturality? 
_⇿_ : Container → Container → Set₁
C₁ ⇿ C₂ = ∀ X → ⟦ C₁ ⟧ᶜ X ↔ ⟦ C₂ ⟧ᶜ X

con-map : (A → B) → ⟦ C ⟧ᶜ A → ⟦ C ⟧ᶜ B 
con-map f ⟨ s , p ⟩ = ⟨ s , f ∘ p ⟩

instance
  con-functor : Functor ⟦ C ⟧ᶜ
  con-functor .fmap                 = con-map
  con-functor .fmap-id ⟨ s , p ⟩    = refl
  con-functor .fmap-∘ f g ⟨ s , p ⟩ = refl 

injˡ : ∀ C₂ → C₁ ↦ (C₁ ⊕ᶜ C₂)
injˡ _ ⟨ c , k ⟩ = ⟨ inj₁ c , k ⟩

injʳ : ∀ C₁ → C₂ ↦ (C₁ ⊕ᶜ C₂)
injʳ _ ⟨ c , k ⟩ = ⟨ (inj₂ c , k) ⟩

swapᶜ : (C₁ ⊕ᶜ C₂) ↦ (C₂ ⊕ᶜ C₁)
swapᶜ ⟨ inj₁ c , k ⟩ = ⟨ inj₂ c , k ⟩
swapᶜ ⟨ inj₂ c , k ⟩ = ⟨ inj₁ c , k ⟩

swapᶜ-involutive : ∀ (x : ⟦ C₁ ⊕ᶜ C₂ ⟧ᶜ A) → swapᶜ {C₂} {C₁} (swapᶜ {C₁} {C₂} x) ≡ x
swapᶜ-involutive ⟨ inj₁ x , k ⟩ = refl
swapᶜ-involutive ⟨ inj₂ y , k ⟩ = refl

swapᶜ-↔ : (C₁ ⊕ᶜ C₂) ⇿ (C₂ ⊕ᶜ C₁)
swapᶜ-↔ {C₁} {C₂} X = record
  { to        = swapᶜ {C₁} {C₂}
  ; from      = swapᶜ {C₂} {C₁}
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = swapᶜ-involutive , swapᶜ-involutive
  }

swapᶜ-↔-natural : ∀ C₁ C₂ → NaturalIsomorphism (swapᶜ-↔ {C₁} {C₂})
swapᶜ-↔-natural _ _ = record
  { to-natural   = λ where
      .commute ⟨ inj₁ x , k ⟩ → refl
      .commute ⟨ inj₂ y , k ⟩ → refl
  ; from-natural = λ where
      .commute ⟨ inj₁ x , k ⟩ → refl
      .commute ⟨ inj₂ y , k ⟩ → refl
  } 

assocᶜʳ : ((C₁ ⊕ᶜ C₂) ⊕ᶜ C₃) ↦ (C₁ ⊕ᶜ (C₂ ⊕ᶜ C₃))
assocᶜʳ ⟨ inj₁ (inj₁ c) , k ⟩ = ⟨ inj₁ c , k ⟩
assocᶜʳ ⟨ inj₁ (inj₂ c) , k ⟩ = ⟨ (inj₂ (inj₁ c) , k) ⟩
assocᶜʳ ⟨ inj₂ c        , k ⟩ = ⟨ (inj₂ (inj₂ c) , k) ⟩

assocᶜˡ : (C₁ ⊕ᶜ (C₂ ⊕ᶜ C₃)) ↦ ((C₁ ⊕ᶜ C₂) ⊕ᶜ C₃ ) 
assocᶜˡ ⟨ inj₁ c        , k ⟩ = ⟨ (inj₁ (inj₁ c) , k) ⟩
assocᶜˡ ⟨ inj₂ (inj₁ c) , k ⟩ = ⟨ ((inj₁ (inj₂ c)) , k) ⟩
assocᶜˡ ⟨ inj₂ (inj₂ c) , k ⟩ = ⟨ inj₂ c , k ⟩

assocᶜ-↔ : (C₁ ⊕ᶜ (C₂ ⊕ᶜ C₃)) ⇿ ((C₁ ⊕ᶜ C₂) ⊕ᶜ C₃) 
assocᶜ-↔ {C₁} {C₂} {C₃} _ = record
  { to        = assocᶜˡ {C₁} {C₂} {C₃}
  ; from      = assocᶜʳ {C₁} {C₂} {C₃}
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = assoc-inverseˡ , assoc-inverseʳ
  }
  where
    assoc-inverseˡ : ∀ x → assocᶜˡ (assocᶜʳ {C₁} {C₂} {C₃} x) ≡ x
    assoc-inverseˡ ⟨ inj₁ (inj₁ _) , _ ⟩ = refl
    assoc-inverseˡ ⟨ inj₁ (inj₂ _) , _ ⟩ = refl
    assoc-inverseˡ ⟨ inj₂ _        , _ ⟩ = refl

    assoc-inverseʳ : ∀ x → assocᶜʳ (assocᶜˡ {C₁} {C₂} {C₃} x) ≡ x
    assoc-inverseʳ ⟨ inj₁ _        , _ ⟩ = refl
    assoc-inverseʳ ⟨ inj₂ (inj₁ _) , _ ⟩ = refl
    assoc-inverseʳ ⟨ inj₂ (inj₂ _) , _ ⟩ = refl

assocᶜ-natiso : ∀ C₁ C₂ C₃ → NaturalIsomorphism (assocᶜ-↔ {C₁} {C₂} {C₃})
assocᶜ-natiso _ _ _ = record
  { to-natural   = λ where
      .commute ⟨ inj₁ c        , k ⟩ → refl
      .commute ⟨ inj₂ (inj₁ c) , k ⟩ → refl
      .commute ⟨ inj₂ (inj₂ c) , k ⟩ → refl
  ; from-natural = λ where
      .commute ⟨ inj₁ (inj₁ c) , k ⟩ → refl
      .commute ⟨ inj₁ (inj₂ c) , k ⟩ → refl
      .commute ⟨ inj₂ c        , k ⟩ → refl
  } 

open Inverse 

⊕ᶜ-congˡ : C₁ ⇿ C₂ → (C₁ ⊕ᶜ C) ⇿ (C₂ ⊕ᶜ C)
⊕ᶜ-congˡ {C₁} {C₂} {C} iso X = record
  { to        = to′
  ; from      = from′
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = cong-inverseˡ , cong-inverseʳ
  }
  where
    to′ : (C₁ ⊕ᶜ C) ↦ (C₂ ⊕ᶜ C)
    to′ ⟨ inj₁ c , k ⟩ = injˡ C (iso _ .to ⟨ (c , k) ⟩)
    to′ ⟨ inj₂ c , k ⟩ = ⟨ (inj₂ c , k) ⟩

    from′ : (C₂ ⊕ᶜ C) ↦ (C₁ ⊕ᶜ C)
    from′ ⟨ inj₁ c , k ⟩ = injˡ C (iso _ .from ⟨ c , k ⟩)
    from′ ⟨ inj₂ c , k ⟩ = ⟨ (inj₂ c , k) ⟩

    cong-inverseˡ : ∀ x → to′ (from′ x) ≡ x
    cong-inverseˡ ⟨ inj₁ c , k ⟩ = cong (injˡ C) (iso _ .inverse .proj₁ _) 
    cong-inverseˡ ⟨ inj₂ c , k ⟩ = refl
    
    cong-inverseʳ : ∀ x → from′ (to′ x) ≡ x 
    cong-inverseʳ ⟨ inj₁ c , k ⟩ = cong (injˡ C) (iso _ .inverse. proj₂ _)
    cong-inverseʳ ⟨ inj₂ c , k ⟩ = refl

⊕ᶜ-congˡ-natiso :
  ∀ C₁ C₂ C
  → (eq : C₁ ⇿ C₂) (natural : NaturalIsomorphism eq)
  → NaturalIsomorphism (⊕ᶜ-congˡ {C₁} {C₂} {C} eq)
⊕ᶜ-congˡ-natiso C₁ C₂ C eq natural = record
  { to-natural   = λ where
      .commute {f = f} ⟨ inj₁ c , k ⟩ →
         cong (injˡ C) (natural .to-natural .commute {f = f} ⟨ c , k ⟩) 
      .commute ⟨ inj₂ y , k ⟩ → refl
  ; from-natural = λ where
      .commute {f = f} ⟨ inj₁ c , k ⟩ →
        cong (injˡ C) (natural .from-natural .commute {f = f} ⟨ c , k ⟩)
      .commute {f = f} ⟨ inj₂ c , k ⟩ → refl
  }
  where open ≡-Reasoning

⊕ᶜ-congʳ : C₁ ⇿ C₂ → (C ⊕ᶜ C₁) ⇿ (C ⊕ᶜ C₂)
⊕ᶜ-congʳ {C₁} {C₂} {C} iso X = record
  { to        = to′
  ; from      = from′
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = cong-inverseˡ , cong-inverseʳ
  }
  where
    to′ : (C ⊕ᶜ C₁) ↦ (C ⊕ᶜ C₂)
    to′ ⟨ inj₁ c , k ⟩ = ⟨ inj₁ c , k ⟩
    to′ ⟨ inj₂ c , k ⟩ = injʳ C (iso _ .to ⟨ c , k ⟩)

    from′ : (C ⊕ᶜ C₂) ↦ (C ⊕ᶜ C₁)
    from′ ⟨ inj₁ c , k ⟩ = ⟨ inj₁ c , k ⟩
    from′ ⟨ inj₂ c , k ⟩ = injʳ C (iso _ .from ⟨ (c , k) ⟩)

    cong-inverseˡ : ∀ x → to′ (from′ x) ≡ x
    cong-inverseˡ ⟨ inj₁ x , k ⟩ = refl
    cong-inverseˡ ⟨ inj₂ y , k ⟩ = cong (injʳ C) (iso _ .inverse. proj₁ _)
    
    cong-inverseʳ : ∀ x → from′ (to′ x) ≡ x 
    cong-inverseʳ ⟨ inj₁ x , k ⟩ = refl
    cong-inverseʳ ⟨ inj₂ y , k ⟩ = cong (injʳ C) (iso _ .inverse .proj₂ _)

⊕ᶜ-congʳ-natiso :
  ∀ C₁ C₂ C
  → (eq : C₁ ⇿ C₂) (natural : NaturalIsomorphism eq)
  → NaturalIsomorphism (⊕ᶜ-congʳ {C₁} {C₂} {C} eq)
⊕ᶜ-congʳ-natiso C₁ C₂ C eq natural = record
  { to-natural   = λ where
      .commute ⟨ inj₁ c , k ⟩ → refl
      .commute {f = f} ⟨ inj₂ c , k ⟩ →
        cong (injʳ C) (natural .to-natural .commute {f = f} ⟨ c , k ⟩)
  ; from-natural = λ where
      .commute ⟨ inj₁ c , k ⟩ → refl
      .commute {f = f} ⟨ inj₂ c , k ⟩ →
        cong (injʳ C) (natural .from-natural .commute {f = f } ⟨ c , k ⟩)
  }

⊥ᶜ : Container
⊥ᶜ = record { shape = ⊥ ; position = λ() } 

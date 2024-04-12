{-# OPTIONS --without-K #-} 

open import Relation.Unary
open import Function 
open import Data.Product 
open import Data.Sum
open import Data.Empty

open import Core.Functor
open import Core.Functor.NaturalTransformation
open import Core.Functor.HigherOrder
open import Core.Extensionality

open import Relation.Binary using (Reflexive ; Transitive ; Symmetric)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Function
open import Function.Construct.Identity hiding (inverse)
open import Function.Construct.Symmetry hiding (inverse)
open import Function.Construct.Composition hiding (inverse)

module Core.Signature where

open ≡-Reasoning

record Signature : Set₁ where
  no-eta-equality
  field
    command  : Set
    response : command → Set

    fork     : command → Set
    returns  : {c : command} → (ψ : fork c) → Set 

  -- The reflection (extension) of a signature as an endofunctor on [set,set]. 
  record ⟦_⟧ (M : Set → Set) (A : Set) : Set where
    constructor ⟪_⟫ 
    field reflect : Σ command λ c → (response c → M A) × ((ψ : fork c) → M (returns ψ))

  open ⟦_⟧ public 

  record Algebra (F : Set → Set) : Set₁ where
    field α : ∀[ ⟦_⟧ F ⇒ F ] 

  open Algebra public 

open Signature public 

variable σ σ₁ σ₂ σ₃ σ′ : Signature

_⊕_ : (_ _ : Signature) → Signature
σ₁ ⊕ σ₂ = record
  { command  = σ₁ .command ⊎ σ₂ .command
  ; response = [ σ₁ .response , σ₂ .response ]
  ; fork     = [ σ₁ .fork , σ₂ .fork ]
  ; returns  = λ where {inj₁ c} → σ₁ .returns
                       {inj₂ c} → σ₂ .returns 
  }

_·⊕_ : {A : Set a} → (_ _ : A → Signature) → A → Signature
(P ·⊕ Q) x = P x ⊕ Q x

_⟨⊕⟩_ : ∀[ Algebra σ₁ ⇒ Algebra σ₂ ⇒ Algebra (σ₁ ⊕ σ₂) ]
(x ⟨⊕⟩ y) .α ⟪ inj₁ c , r , s ⟫ = x .α ⟪ c , r , s ⟫
(x ⟨⊕⟩ y) .α ⟪ inj₂ c , r , s ⟫ = y .α ⟪ c , r , s ⟫

sig-hmap : ∀[ F ⇒ G ] → ∀[ ⟦ σ ⟧ F ⇒ ⟦ σ ⟧ G ]
sig-hmap θ ⟪ c , r , s ⟫ = ⟪ c , θ ∘ r , θ ∘ s  ⟫


-- The semantics of signatures maps functors to functors 
instance
  sig-functor : ⦃ Functor F ⦄ → Functor (⟦ σ ⟧ F)
  sig-functor .fmap f  ⟪ c , r , s ⟫ = ⟪ c , fmap f ∘ r , s ⟫
  sig-functor {F = F} .fmap-id
    = extensionality λ where ⟪ c , r , s ⟫ → cong (λ ○ → ⟪ c , ○ , s ⟫) (cong (_∘ r) $ fmap-id {F = F})
  sig-functor .fmap-∘  f g =
    extensionality λ where ⟪ c , r , s ⟫ → cong (λ ○ → ⟪ c , ○ , s ⟫) (cong (_∘ r) (fmap-∘ f g)) 

instance 
  sig-hfunctor : HFunctor ⟦ σ ⟧
  sig-hfunctor .HF-functor = sig-functor 
  sig-hfunctor .hmap θ ⟪ c , r , s ⟫ = ⟪ c , θ ∘ r , θ ∘ s ⟫
  sig-hfunctor .hmap-natural θ nt .commute {f = f} ⟪ c , r , s ⟫ =
    begin
      ⟪ c , θ ∘ fmap f ∘ r , θ ∘ s ⟫
    ≡⟨ cong₂ (λ ○₁ ○₂ → ⟪ c , ○₁ , ○₂ ⟫) (extensionality $ nt .commute ∘ r) refl ⟩
      ⟪ c , fmap f ∘ θ ∘ r , θ ∘ s ⟫
    ∎

open Inverse

module _ where 

  -- Analogous to container morphisms, morphisms of signatures are the natural
  -- transformations between their extension functors
  _↦ᴴ_ : Signature → Signature → Set₁
  σ₁ ↦ᴴ σ₂ = ∀ {F} → ∀[ ⟦ σ₁ ⟧ F ⇒ ⟦ σ₂ ⟧ F ]  

  injᴴˡ : σ₁ ↦ᴴ (σ₁ ⊕ σ₂)
  injᴴˡ ⟪ c , k , s ⟫ = ⟪ inj₁ c , k , s ⟫
  
  injᴴʳ : σ₂ ↦ᴴ (σ₁ ⊕ σ₂)
  injᴴʳ ⟪ c , k , s ⟫ = ⟪ inj₂ c , k , s ⟫

  record _⇿ᴴ_ (σ₁ σ₂ : Signature) : Set₁ where
    field
      equivalenceᴴ : ∀ F X → ⟦ σ₁ ⟧ F X ↔ ⟦ σ₂ ⟧ F X
      -- TODO: do we require proofs of naturality for this relation as well? 


  open _⇿ᴴ_ public 

  ⇿ᴴ-refl : Reflexive _⇿ᴴ_
  ⇿ᴴ-refl =
    record { equivalenceᴴ = λ _ _ → ↔-id _ } 

  ⇿ᴴ-sym : Symmetric _⇿ᴴ_
  ⇿ᴴ-sym eq =
    record { equivalenceᴴ = λ _ _ → ↔-sym (eq .equivalenceᴴ _ _) }

  ⇿ᴴ-trans : Transitive _⇿ᴴ_
  ⇿ᴴ-trans eq₁ eq₂ =
    record { equivalenceᴴ = λ F X → eq₂ .equivalenceᴴ F X ↔-∘ eq₁ .equivalenceᴴ F X }

⊥-sig : Signature
⊥-sig = record
  { command  = ⊥
  ; response = λ()
  ; fork     = λ()
  ; returns  = (λ where {c = ()})
  }

swap-sig : (σ₁ ⊕ σ₂) ↦ᴴ (σ₂ ⊕ σ₁)
swap-sig ⟪ inj₁ c , k , s ⟫ = ⟪ inj₂ c , k , s ⟫
swap-sig ⟪ inj₂ c , k , s ⟫ = ⟪ inj₁ c , k , s ⟫

swap-sig-involutive : (x : ⟦ σ₁ ⊕ σ₂ ⟧ F A) → swap-sig (swap-sig x) ≡ x
swap-sig-involutive ⟪ inj₁ c , k , s ⟫ = refl
swap-sig-involutive ⟪ inj₂ y , k , s ⟫ = refl

swap-sig-⇿ᴴ : (σ₁ ⊕ σ₂) ⇿ᴴ (σ₂ ⊕ σ₁)
equivalenceᴴ swap-sig-⇿ᴴ F X = record
  { to        = swap-sig
  ; from      = swap-sig
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = (λ where refl → swap-sig-involutive _) , λ where refl → swap-sig-involutive _
  }

assoc-sigʳ : ((σ₁ ⊕ σ₂) ⊕ σ₃) ↦ᴴ (σ₁ ⊕ (σ₂ ⊕ σ₃))  
assoc-sigʳ ⟪ inj₁ (inj₁ c) , k , s ⟫ = ⟪ inj₁ c , k , s ⟫
assoc-sigʳ ⟪ inj₁ (inj₂ c) , k , s ⟫ = ⟪ inj₂ (inj₁ c) , k , s ⟫
assoc-sigʳ ⟪ inj₂ c        , k , s ⟫ = ⟪ inj₂ (inj₂ c) , k , s ⟫

assoc-sigˡ : (σ₁ ⊕ (σ₂ ⊕ σ₃)) ↦ᴴ ((σ₁ ⊕ σ₂) ⊕ σ₃)
assoc-sigˡ ⟪ inj₁ c        , k , s ⟫ = ⟪ inj₁ (inj₁ c) , k , s ⟫
assoc-sigˡ ⟪ inj₂ (inj₁ c) , k , s ⟫ = ⟪ inj₁ (inj₂ c) , k , s ⟫
assoc-sigˡ ⟪ inj₂ (inj₂ c) , k , s ⟫ = ⟪ inj₂ c , k , s ⟫

assoc-sig-⇿ᴴ : ((σ₁ ⊕ σ₂) ⊕ σ₃) ⇿ᴴ (σ₁ ⊕ (σ₂ ⊕ σ₃)) 
equivalenceᴴ assoc-sig-⇿ᴴ F X = record
  { to        = assoc-sigʳ
  ; from      = assoc-sigˡ
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = (λ where {x} refl → assoc-inverseʳ x) , λ where {x} refl → assoc-inverseˡ x
  }
  where
    assoc-inverseˡ : ∀ x → assoc-sigˡ (assoc-sigʳ x) ≡ x
    assoc-inverseˡ ⟪ inj₁ (inj₁ _) , _ , _ ⟫ = refl
    assoc-inverseˡ ⟪ inj₁ (inj₂ _) , _ , _ ⟫ = refl
    assoc-inverseˡ ⟪ inj₂ _        , _ , _ ⟫ = refl

    assoc-inverseʳ : ∀ x → assoc-sigʳ (assoc-sigˡ x) ≡ x
    assoc-inverseʳ ⟪ inj₁ _        , _ , _ ⟫ = refl
    assoc-inverseʳ ⟪ inj₂ (inj₁ _) , _ , _ ⟫ = refl
    assoc-inverseʳ ⟪ inj₂ (inj₂ _) , _ , _ ⟫ = refl

⊕-congˡ : σ₁ ⇿ᴴ σ₂ → (σ₁ ⊕ σ) ⇿ᴴ (σ₂ ⊕ σ)
equivalenceᴴ (⊕-congˡ {σ₁}{σ₂}{σ} eq) F X = record
  { to        = to′
  ; from      = from′
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = (λ where refl → cong-inverseˡ _) , λ where refl → cong-inverseʳ _
  }
  where
    to′ : (σ₁ ⊕ σ) ↦ᴴ (σ₂ ⊕ σ)
    to′ ⟪ inj₁ c , k , s ⟫ = injᴴˡ (eq .equivalenceᴴ _ _ .to ⟪ c , k , s ⟫)
    to′ ⟪ inj₂ c , k , s ⟫ = ⟪ inj₂ c , k , s ⟫

    from′ : (σ₂ ⊕ σ) ↦ᴴ (σ₁ ⊕ σ)
    from′ ⟪ inj₁ c , k , s ⟫ = injᴴˡ (eq .equivalenceᴴ _ _ .from ⟪ c , k , s ⟫)
    from′ ⟪ inj₂ c , k , s ⟫ = ⟪ inj₂ c , k , s ⟫

    cong-inverseˡ : ∀ x → to′ (from′ x) ≡ x 
    cong-inverseˡ ⟪ inj₁ c , k , s ⟫ = cong injᴴˡ (eq .equivalenceᴴ _ _ .inverse .proj₁ refl)
    cong-inverseˡ ⟪ inj₂ c , k , s ⟫ = refl

    cong-inverseʳ : ∀ x → from′ (to′ x) ≡ x
    cong-inverseʳ ⟪ inj₁ c , k , s ⟫ = cong injᴴˡ (eq .equivalenceᴴ _ _ .inverse .proj₂ refl)
    cong-inverseʳ ⟪ inj₂ c , k , s ⟫ = refl


⊕-congʳ : σ₁ ⇿ᴴ σ₂ → (σ ⊕ σ₁) ⇿ᴴ (σ ⊕ σ₂)
equivalenceᴴ (⊕-congʳ {σ₁}{σ₂}{σ} eq) F X = record
  { to        = to′
  ; from      = from′
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = (λ where refl → cong-inverseˡ _) , λ where refl → cong-inverseʳ _
  }
  where
    to′ : (σ ⊕ σ₁) ↦ᴴ (σ ⊕ σ₂)
    to′ ⟪ inj₁ c , k , s ⟫ = ⟪ inj₁ c , k , s ⟫ 
    to′ ⟪ inj₂ c , k , s ⟫ = injᴴʳ (eq .equivalenceᴴ _ _ .to ⟪ c , k , s ⟫)

    from′ : (σ ⊕ σ₂) ↦ᴴ (σ ⊕ σ₁)
    from′ ⟪ inj₁ c , k , s ⟫ = ⟪ inj₁ c , k , s ⟫ 
    from′ ⟪ inj₂ c , k , s ⟫ = injᴴʳ (eq .equivalenceᴴ _ _ .from ⟪ c , k , s ⟫)

    cong-inverseˡ : ∀ x → to′ (from′ x) ≡ x 
    cong-inverseˡ ⟪ inj₁ c , k , s ⟫ = refl  
    cong-inverseˡ ⟪ inj₂ c , k , s ⟫ = cong injᴴʳ (eq .equivalenceᴴ _ _ .inverse .proj₁ refl)

    cong-inverseʳ : ∀ x → from′ (to′ x) ≡ x
    cong-inverseʳ ⟪ inj₁ c , k , s ⟫ = refl
    cong-inverseʳ ⟪ inj₂ c , k , s ⟫ = cong injᴴʳ (eq .equivalenceᴴ _ _ .inverse .proj₂ refl)

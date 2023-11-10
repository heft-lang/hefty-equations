open import Free.Base
open import Hefty.Base

open import Core.Functor
open import Core.Signature

open import Effect.Base
open import Effect.Theory.FirstOrder

open import Data.Product hiding (map)
open import Data.Nat 
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Vec hiding (map ; _++_)

open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Function 

{- Theories for higher-order effects. Built on Zhixuan Yang and Nicholas Wu's
paper, but adapted for use with Hefty algebras -}

module Effect.Theory.HigherOrder where

record Equationᴴ (η : Effectᴴ) (Δ : ℕ) (Γ R : Vec Set Δ → Set) : Set₁ where
  constructor _≗ᴴ_
  field
    lhsᴴ rhsᴴ : (δ : Vec Set Δ) → Γ δ → Hefty η (R δ)

open Equationᴴ public

embed-equation : Equation ε Δ Γ R → Equationᴴ (↑ ε) Δ Γ R
embed-equation eq = (embed-free ∘₂ eq .lhs) ≗ᴴ (embed-free ∘₂ eq .lhs)

-- Weakening of equations (for higher-order effects). That is, `Equationᴴ`
-- defines a functor over the category of h.o. effects
wk-equationᴴ : ⦃ η₁ ⊑ᴴ η₂ ⦄ → ∀[ Equationᴴ η₁ Δ Γ ⇒ Equationᴴ η₂ Δ Γ ]
wk-equationᴴ eq = (♯ᴴ ∘₂ eq .lhsᴴ) ≗ᴴ (♯ᴴ ∘₂ eq .rhsᴴ) 

-- Again, an algebra respects an equation if folding lhs and rhs gives the same
-- result, where "sameness" is with respect a given binary relation that is kept
-- abstract here.
-- 
-- We opt for this generalization (rather than using propositional equality)
-- here, because later we define correctness of elaborations as
Respectsᴴ : (_~_ : ∀ {A} → F A → F A → Set₁) → Algebra η F → Equationᴴ η Δ Γ R → Set₁
Respectsᴴ _~_ alg (lhs ≗ᴴ rhs) =
  ∀ {δ γ} {k : ∀[ id ⇒ _ ]} → fold-hefty k alg (lhs δ γ) ~ fold-hefty k alg (rhs δ γ)


-- Theories of higher-order effects are collections of equations
record Theoryᴴ (η : Effectᴴ) : Set₁ where
  no-eta-equality
  constructor ∥_∥ᴴ
  field
    equationsᴴ : List $ ∃ λ Δ → ∃₂ $ Equationᴴ η Δ 

open Theoryᴴ public

◇_ : Equationᴴ η Δ Γ R → ∃ λ Δ → ∃₂ $ Equationᴴ η Δ
◇ eq = -, -, -, eq 

variable Th Th₁ Th₂ Th₃ Th′ : Theoryᴴ η 

-- A predicate asserting that a given equation is part of a theory
_◃ᴴ_ : Equationᴴ η Δ Γ R → Theoryᴴ η → Set₁
eq ◃ᴴ Th = (-, -, -, eq) ∈ Th .equationsᴴ

-- Theory inclusion for higher-order theories
_⊆ᴴ_ : Theoryᴴ η → Theoryᴴ η → Set₁
Th₁ ⊆ᴴ Th₂ = ∀ {Δ Γ} {A} {eq : Equationᴴ _ Δ Γ A} → eq ◃ᴴ Th₁ → eq ◃ᴴ Th₂

embed-theory : Theory ε → Theoryᴴ (↑ ε)
embed-theory T .equationsᴴ = map (λ (_ , _ , _ , eq) → -, -, -, embed-equation eq) (T .equations)

wk-theoryᴴ : ⦃ η₁ ⊑ᴴ η₂ ⦄ → Theoryᴴ η₁ → Theoryᴴ η₂ 
wk-theoryᴴ eq = ∥ map (λ where (_ , _ , _ , eq) → -, -, -, wk-equationᴴ eq) (eq .equationsᴴ) ∥ᴴ

-- Coproduct of higher-order effect theories
_⟨+⟩ᴴ_ : ∀[ Theoryᴴ ⇒ Theoryᴴ ⇒ Theoryᴴ ]
(Th₁ ⟨+⟩ᴴ Th₂) .equationsᴴ = Th₁ .equationsᴴ ++ Th₂ .equationsᴴ

_[+]ᴴ_ : Theoryᴴ η₁ → Theoryᴴ η₂ → Theoryᴴ (η₁ ⊕ η₂)
Th₁ [+]ᴴ Th₂ = wk-theoryᴴ ⦃ ⊑ᴴ-⊕-left ⦄ Th₁ ⟨+⟩ᴴ wk-theoryᴴ ⦃ ⊑ᴴ-⊕-right ⦄ Th₂

-- Syntactic equivalence of programs with higher order effects, with respect to
-- a given theory `Th`. Analagous to how we defined syntactic equivalence for
-- first-order effect trees
infix 2 _≋⟨_⟩_
data _≋⟨_⟩_ {η} : (m₁ : Hefty η A) → Theoryᴴ η → (m₂ : Hefty η A) → Set₁ where

  ≋-refl  : ------------
            m ≋⟨ Th ⟩ m

  ≋-sym   : m₁ ≋⟨ Th ⟩ m₂
            -------------
          → m₂ ≋⟨ Th ⟩ m₁

  ≋-trans : m₁ ≋⟨ Th ⟩ m₂
          → m₂ ≋⟨ Th ⟩ m₃
            -------------
          → m₁ ≋⟨ Th ⟩ m₃

  ≋-cong  : (c : η .command)
          → (r₁ r₂ : η .response c → Hefty η A)
          → (s₁ s₂ : (ψ : η .fork c) → Hefty η (η .returns ψ))
          → (∀ {x} → r₁ x ≋⟨ Th ⟩ r₂ x)
          → (∀ {ψ} → s₁ ψ ≋⟨ Th ⟩ s₂ ψ)  
            -----------------------------------------------------
          → impure ⟪ c , r₁ , s₁ ⟫ ≋⟨ Th ⟩ impure ⟪ c , r₂ , s₂ ⟫

  ≋-eq    : (eq : Equationᴴ η Δ Γ R)
          → eq ◃ᴴ Th
          → (δ : Vec Set Δ)
          → (γ : Γ δ)
          → (k : R δ → Hefty η B)
            -----------------------------------------------
          → eq .rhsᴴ δ γ >>= k ≋⟨ Th ⟩ (eq .rhsᴴ δ γ >>= k)


Correctᴴ : Theoryᴴ η → Theory ε → Elaboration η ε → Set₁ 
Correctᴴ Th T e =
  ∀ {Δ Γ A} {eq : Equationᴴ _ Δ Γ A} → eq ◃ᴴ Th → Respectsᴴ (_≈⟨ T ⟩_) (e .elab) eq 


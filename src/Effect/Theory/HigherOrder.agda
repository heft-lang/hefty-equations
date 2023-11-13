open import Free.Base
open import Hefty.Base

open import Core.Functor
open import Core.Signature
open import Core.Extensionality

open import Effect.Base
open import Effect.Theory.FirstOrder


open import Data.List hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any hiding (map)

open import Data.Vec hiding (map ; _++_ ; [_])
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Nat

open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)

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
Respectsᴴ : (_~_ : ∀ {A} → Free ε A → Free ε A → Set₁) → Algebra η (Free ε) → Equationᴴ η Δ Γ R → Set₁
Respectsᴴ _~_ alg (lhs ≗ᴴ rhs) =
  ∀ {δ γ} → fold-hefty pure alg (lhs δ γ) ~ fold-hefty pure alg (rhs δ γ)


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




{- Correctness of elaborations -} 


-- We say that an elaboration is correct with respect to some higher-order
-- effect theory of its higher-order effect, and some first-order effect theory
-- of the algebraic effects it elaborates into iff the elaboration algebra
-- respects all equations of the higher-order theory modulo syntactic
-- equivalence of the resulting effect trees with respect to the first-order
-- effect theory. 
Correctᴴ : Theoryᴴ η → Theory ε → Elaboration η ε → Set₁ 
Correctᴴ Th T e =
  ∀ {Δ Γ A} {eq : Equationᴴ _ Δ Γ A} → eq ◃ᴴ Th → Respectsᴴ (_≈⟨ T ⟩_) (e .elab) eq 


-- Equations that occur in a composed theory can be found in either of the
-- argument theories
[+]ᴴ-injective : ∀ Th₁ Th₂ {eq : Equationᴴ (η₁ ⊕ η₂) Δ Γ R}
         → eq ◃ᴴ (Th₁ [+]ᴴ Th₂)
         →   (eq ◃ᴴ wk-theoryᴴ ⦃ ⊑ᴴ-⊕-left  ⦄ Th₁ )
           ⊎ (eq ◃ᴴ wk-theoryᴴ ⦃ ⊑ᴴ-⊕-right ⦄ Th₂ )
[+]ᴴ-injective Th₁ Th₂ {eq} px with Th₁ .equationsᴴ
... | []      = inj₂ px
... | x ∷ eqs =
  case px of
    λ where (here refl) → inj₁ (here refl)
            (there px′) →
              [ inj₁ ∘ there
              , inj₂
              ] $ [+]ᴴ-injective (λ where .equationsᴴ → eqs) Th₂ px′

-- Equations of a weakened theory are themselves weakened equations 
◃ᴴ-weaken-lemma : ∀ Th (w : η₁ ⊑ᴴ η₂)
       → (eq : Equationᴴ η₂ Δ Γ R)
       → eq ◃ᴴ wk-theoryᴴ ⦃ w ⦄ Th
       → ∃ λ (eq′ : Equationᴴ η₁ Δ Γ R) → eq′ ◃ᴴ Th × eq ≡ wk-equationᴴ ⦃ w ⦄ eq′ 
◃ᴴ-weaken-lemma Th w eq px with Th .equationsᴴ
... | eq′ ∷ eqs =
  case px of
    λ where (here refl) → _ , here refl , refl
            (there px′) →
              case ◃ᴴ-weaken-lemma (λ where .equationsᴴ → eqs) w eq px′ of
                λ where (a , px′′ , refl) → a , there px′′ , refl 

map-id : (m : Hefty η A) → map-hefty id m ≡ m
map-id (pure x)               = refl
map-id (impure ⟪ c , r , s ⟫) =
  cong₂
    (λ □₁ □₂ → impure ⟪ c , □₁ , □₂ ⟫)
    (extensionality (map-id ∘ r))
    refl

⟨⊕⟩-fold-left : ∀ (m : Hefty η A)
                  {f : Algebra η F} {g : Algebra η′ F}
                  {k : ∀[ id ⇒ F ]}
                →   fold-hefty k f m
                  ≡ fold-hefty k (f ⟨⊕⟩ g) (♯ᴴ ⦃ ⊑ᴴ-⊕-left ⦄ m)
⟨⊕⟩-fold-left (pure _)                           = refl
⟨⊕⟩-fold-left (impure ⟪ c , r , s ⟫) {f} {g} {k} =
  cong₂
    (λ □₁ □₂ → f .α ⟪ c , □₁ , □₂ ⟫)
    ( extensionality λ x → ⟨⊕⟩-fold-left $ r x )
    ( extensionality λ x →
        trans
          ( ⟨⊕⟩-fold-left $ s x )
          ( cong
              (λ □ → fold-hefty k (f ⟨⊕⟩ g) □)
              (sym (map-id (♯ᴴ ⦃ ⊑ᴴ-⊕-left ⦄ (s x)))
              ))
    )

⟨⊕⟩-fold-right : ∀ (m : Hefty η A)
                  {f : Algebra η′ F} {g : Algebra η F}
                  {k : ∀[ id ⇒ F ]}
                →   fold-hefty k g m
                  ≡ fold-hefty k (f ⟨⊕⟩ g) (♯ᴴ ⦃ ⊑ᴴ-⊕-right ⦄ m)
⟨⊕⟩-fold-right (pure _)                           = refl
⟨⊕⟩-fold-right (impure ⟪ c , r , s ⟫) {f} {g} {k} =
  cong₂
    (λ □₁ □₂ → g .α ⟪ c , □₁ , □₂ ⟫)
    ( extensionality λ x → ⟨⊕⟩-fold-right $ r x )
    ( extensionality λ x →
        trans
          ( ⟨⊕⟩-fold-right $ s x )
          ( cong
              (λ □ → fold-hefty k (f ⟨⊕⟩ g) □)
              (sym (map-id (♯ᴴ ⦃ ⊑ᴴ-⊕-right ⦄ (s x)))
              ))
    )


module _ {T : Theory ε} where

  open ≈-Reasoning T 

  ⟪⊕⟫-correct  : ∀ {e₁ e₂}
                 → Correctᴴ Th₁ T e₁
                 → Correctᴴ Th₂ T e₂
                 → Correctᴴ (Th₁ [+]ᴴ Th₂) T (e₁ ⟪⊕⟫ e₂)
  ⟪⊕⟫-correct  {Th₁ = Th₁} {Th₂ = Th₂} cr₁ cr₂ px
    with [+]ᴴ-injective Th₁ Th₂ px 
  ⟪⊕⟫-correct {Th₁ = Th₁} {Th₂ = Th₂} cr₁ cr₂ px
    | inj₁ px′ with ◃ᴴ-weaken-lemma Th₁ ⊑ᴴ-⊕-left _ px′
  ⟪⊕⟫-correct cr₁ cr₂ px | inj₁ px′ | eq′ , px′′ , refl =
    ≈-trans
      ( ≡-to-≈ $ sym $ ⟨⊕⟩-fold-left (eq′ .lhsᴴ _ _) )
      ( ≈-trans
          (cr₁ px′′)
          ( ≡-to-≈ $ ⟨⊕⟩-fold-left (eq′ .rhsᴴ _ _) )
      )
  ⟪⊕⟫-correct {Th₁ = Th₁} {Th₂ = Th₂} cr₁ cr₂ px
    | inj₂ px′ with ◃ᴴ-weaken-lemma Th₂ ⊑ᴴ-⊕-right _ px′
  ⟪⊕⟫-correct cr₁ cr₂ px | inj₂ px′ | eq′ , px′′ , refl =
    ≈-trans
      ( ≡-to-≈ $ sym $ ⟨⊕⟩-fold-right (eq′ .lhsᴴ _ _) )
      ( ≈-trans
          (cr₂ px′′)
          (≡-to-≈ $ ⟨⊕⟩-fold-right (eq′ .rhsᴴ _ _) )
      ) 

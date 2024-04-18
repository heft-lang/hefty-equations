{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Functor.Monad

open import Core.Ternary
open import Core.Logic
open import Core.Signature
open import Core.Extensionality
open import Core.MonotonePredicate 

open import Effect.Base
open import Effect.Theory.FirstOrder
open import Effect.Elaborate

open import Effect.Syntax.Free
open import Effect.Syntax.Hefty

open import Effect.Relation.Binary.FirstOrderInclusion
open import Effect.Relation.Binary.HigherOrderInclusion
open import Effect.Relation.Ternary.FirstOrderSeparation
open import Effect.Relation.Ternary.HigherOrderSeparation

open import Data.List hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any hiding (map)

open import Data.Vec hiding (map ; _++_ ; [_])
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Nat
open import Data.List using (map)

open import Relation.Unary hiding (_∈_ ; _⊆_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)

open import Function 

{- Theories for higher-order effects. Built on Zhixuan Yang and Nicholas Wu's
paper, but adapted for use with Hefty algebras -}

module Effect.Theory.HigherOrder where

--
-- TODO: this notion of equation seems to be too weak!!!!!!
-- 
record Equationᴴ (η : Effectᴴ) : Set₁ where
  constructor _≗ᴴ_
  field
    {Δ′}      : ℕ
    {Γ′ R′}   : Effect → TypeContext Δ′ → Set 
    lhsᴴ rhsᴴ : {ε : Effect} → Π[ Γ′ ε ⇒ R′ ε ⊢ Hefty (η ε) ]

open Equationᴴ public

embed-equation : Equation ε → Equationᴴ (const $ ↑ ε)
embed-equation eq = (embed-free ∘₂ eq .lhs) ≗ᴴ (embed-free ∘₂ eq .lhs)

-- Weakening of equations (for higher-order effects). That is, `Equationᴴ`
-- defines a functor over the category of h.o. effects
wk-equationᴴ : ⦃ η₁ ≲ η₂ ⦄ → Equationᴴ η₁ → Equationᴴ η₂ 
wk-equationᴴ eq = (♯ᴴ ∘₂ eq .lhsᴴ) ≗ᴴ (♯ᴴ ∘₂ eq .rhsᴴ) 

-- Again, an algebra respects an equation if folding lhs and rhs gives the same
-- result, where "sameness" is with respect a given binary relation that is kept
-- abstract here.
-- 
-- We opt for this generalization (rather than using propositional equality)
-- here, because later we define correctness of elaborations as
Respectsᴴ : (_~_ : ∀ {A} → Free ε A → Free ε A → Set₁) → Algebra (η ε) (Free ε) → Equationᴴ η → Set₁
Respectsᴴ _~_ alg (lhs ≗ᴴ rhs) =
  ∀ {δ γ} → fold-hefty pure alg (lhs δ γ) ~ fold-hefty pure alg (rhs δ γ)

-- Theories of higher-order effects are collections of equations
record Theoryᴴ (η : Effectᴴ)  : Set₁ where
  field
    arity : Set 
    eqs   : arity → □ Equationᴴ η

open Theoryᴴ public 

variable Th Th₁ Th₂ Th₃ Th′ : Theoryᴴ η

-- A predicate asserting that a given equation is part of a theory
_◂ᴴ_ : □ Equationᴴ η → Theoryᴴ η → Set₁
eq ◂ᴴ Th = ∃ λ a → eq ≡ Th .eqs a 

wk-theoryᴴ : η₁ ≲ η₂ → Theoryᴴ η₁ → Theoryᴴ η₂
arity (wk-theoryᴴ i Th) = Th .arity
eqs   (wk-theoryᴴ i Th) = λ a → necessary λ i′ → □⟨ Th .eqs a ⟩ ≲ᴴ-trans i i′

_⟨⊎⟩ᴴ_ : ∀[ Theoryᴴ ⇒ Theoryᴴ ⇒ Theoryᴴ ]
arity (Th₁ ⟨⊎⟩ᴴ Th₂) = Th₁ .arity ⊎ Th₂ .arity
eqs   (Th₁ ⟨⊎⟩ᴴ Th₂) = [ Th₁ .eqs , Th₂ .eqs ]

_[⊎]ᴴ_ : Theoryᴴ η₁ → Theoryᴴ η₂ → Theoryᴴ (η₁ ·⊕ η₂)
Th₁ [⊎]ᴴ Th₂ = wk-theoryᴴ ·⊑-⊕-left Th₁ ⟨⊎⟩ᴴ wk-theoryᴴ ·⊑-⊕-right Th₂

-- Syntactic equivalence of programs with higher order effects, with respect to
-- a given theory `Th`. Analagous to how we defined syntactic equivalence for
-- first-order effect trees
infix 2 _≅⟨_⟩_
data _≅⟨_⟩_ {η η′ : Effectᴴ} ⦃ i : η ≲ η′ ⦄
  : (m₁ : Hefty (η′ ε) A) → Theoryᴴ η → (m₂ : Hefty (η′ ε) A) → Set₁ where

  ≅-refl  : ------------
            m ≅⟨ Th ⟩ m

  ≅-sym   : {m₁ : Hefty (η′ ε) A}
          → m₁ ≅⟨ Th ⟩ m₂
            -------------
          → m₂ ≅⟨ Th ⟩ m₁

  ≅-trans : {m₁ : Hefty (η′ ε) A}
          → m₁ ≅⟨ Th ⟩ m₂
          → m₂ ≅⟨ Th ⟩ m₃
            -------------
          → m₁ ≅⟨ Th ⟩ m₃

  ≅-cong  : (c : η′ ε .command)
          → (r₁ r₂ : η′ ε .response c → Hefty (η′ ε) A)
          → (s₁ s₂ : (ψ : η′ ε .fork c) → Hefty (η′ ε) (η′ ε .returns ψ))
          → (∀ {x} → r₁ x ≅⟨ Th ⟩ r₂ x)
          → (∀ {ψ} → s₁ ψ ≅⟨ Th ⟩ s₂ ψ)  
            -----------------------------------------------------
          → impure ⟪ c , r₁ , s₁ ⟫ ≅⟨ Th ⟩ impure ⟪ c , r₂ , s₂ ⟫

  ≅-eq    : (eq : □ Equationᴴ η)
          → eq ◂ᴴ Th
          → (δ : TypeContext ((□⟨ eq ⟩ i) .Δ′))
          → (γ : (□⟨ eq ⟩ i) .Γ′ ε δ)
          → (k : (□⟨ eq ⟩ i) .R′ ε δ → Hefty (η′ ε) B)
            --------------------------------------------------------------------
          → ((□⟨ eq ⟩ i) .rhsᴴ δ γ) >>= k ≅⟨ Th ⟩ ((□⟨ eq ⟩ i) .rhsᴴ δ γ) >>= k          

{- Correctness of elaborations -} 
open Elaboration 

-- We say that an elaboration is correct with respect to some higher-order
-- effect theory of its higher-order effect, and some first-order effect theory
-- of the algebraic effects it elaborates into iff the elaboration algebra
-- respects all equations of the higher-order theory modulo syntactic
-- equivalence of the resulting effect trees modulo the given first-order effect
-- theory.
--
-- Since the "target" effects of an elaboration are merely a lower bound, the
-- definition of correctness closes over all extensions of this lower bound,
-- weakening the given first-order effect theory T to the universally quantified
-- extension ε′
--
-- TODO: this looks remarkably similar to how we close over "value extensions"
-- when defining extensible langauge fragments in the OOPSLA paper. Can we
-- factor those, and the "theory extensions" used here into a common pattern?
Correctᴴ : Theoryᴴ η → Theory ε → Elaboration η ε → Set₁
Correctᴴ {η = η} {ε} Th T e =
  ∀ {ε′ η′}
  → (e′ : Elaboration η′ ε′)
  → ⦃ ζ : e ⊑ e′ ⦄
  → {eq : □ Equationᴴ η}
  → eq ◂ᴴ Th
    ---------------------------------------------------------
  → Respectsᴴ (_≈⟨ T ⟩_) (□⟨ e′ .elab ⟩ ≲-refl) (□⟨ eq ⟩ ζ .≲-effᴴ)


map-id : (m : Hefty σ A) → map-hefty id m ≡ m
map-id (pure x)               = refl
map-id (impure ⟪ c , r , s ⟫) =
  cong₂
    (λ □₁ □₂ → impure ⟪ c , □₁ , □₂ ⟫)
    (extensionality (map-id ∘ r))
    refl

⟨⊕⟩-fold-left : ∀ (m : Hefty σ A)
                  {f : Algebra σ F} {g : Algebra σ′ F}
                  {k : ∀[ id ⇒ F ]}
                →   fold-hefty k f m
                  ≡ fold-hefty k (f ⟨⊕⟩ g) (♯ᴴ ⦃ ⊑-⊕-left ⦄ m)
⟨⊕⟩-fold-left (pure _)                           = refl
⟨⊕⟩-fold-left (impure ⟪ c , r , s ⟫) {f} {g} {k} =
  cong₂
    (λ □₁ □₂ → f .α ⟪ c , □₁ , □₂ ⟫)   
    ( extensionality λ x → ⟨⊕⟩-fold-left $ r x )
    ( extensionality λ x → ⟨⊕⟩-fold-left $ s x )
   
⟨⊕⟩-fold-right : ∀ (m : Hefty σ A)
                  {f : Algebra σ′ F} {g : Algebra σ F}
                  {k : ∀[ id ⇒ F ]}
                →   fold-hefty k g m
                  ≡ fold-hefty k (f ⟨⊕⟩ g) (♯ᴴ ⦃ ⊑-⊕-right ⦄ m)
⟨⊕⟩-fold-right (pure _)                           = refl
⟨⊕⟩-fold-right (impure ⟪ c , r , s ⟫) {f} {g} {k} =
  cong₂
    (λ □₁ □₂ → g .α ⟪ c , □₁ , □₂ ⟫)
    ( extensionality λ x → ⟨⊕⟩-fold-right $ r x )
    ( extensionality λ x → ⟨⊕⟩-fold-right $ s x )
    

 -- "Homogeneous" composition of correctness proofs for h.o. effect theories.
 --
 -- This theorem establishes that correctness of composed elaborations follows
 -- from correctness of their components, provided they assume the same lower
 -- bound on the algebraic effects for elaboration, and establish correctness
 -- w.r.t. the same first-order effect theory.
[⊎]ᴴ-correct :
  ∀ {e₁ e₂}
  → {Th₁ : Theoryᴴ η₁}
  → {Th₂ : Theoryᴴ η₂}
  → (T : Theory ε)
  → Correctᴴ Th₁ T e₁
  → Correctᴴ Th₂ T e₂
    -------------------------------------
  → Correctᴴ (Th₁ [⊎]ᴴ Th₂) T (e₁ ⟪⊕⟫ e₂)
[⊎]ᴴ-correct {e₁ = e₁} {e₂ = e₂} {Th₁ = Th₁} {Th₂ = Th₂} T C₁ C₂ e′ ⦃ ζ ⦄ {eq} (inj₁ a , refl) 
  = C₁ e′ ⦃ ζ′ ⦄ (a , refl)
  where
    ζ′ : e₁ ⊑ e′
    ≲-eff           ζ′          = ζ .≲-eff
    ≲-effᴴ          ζ′          = ≲ᴴ-trans ·⊑-⊕-left $ ζ .≲-effᴴ
    preserves-cases ζ′ m e′′    = ζ .preserves-cases (injᴴ ⦃ ⊑-⊕-left ⦄ m) e′′
[⊎]ᴴ-correct {e₁ = e₁} {e₂ = e₂} {Th₁ = Th₁} {Th₂ = Th₂} T C₁ C₂ e′ ⦃ ζ ⦄ {eq} (inj₂ a , refl) 
  = C₂ e′ ⦃ ζ′  ⦄ (a , refl)
  where
    ζ′ : e₂ ⊑ e′
    ≲-eff           ζ′          = ζ .≲-eff
    ≲-effᴴ          ζ′          = ≲ᴴ-trans ·⊑-⊕-right $ ζ .≲-effᴴ
    preserves-cases ζ′ m e′′    = ζ .preserves-cases  (injᴴ ⦃ ⊑-⊕-right ⦄ m) e′′

weaken-correct :
  ∀ {T : Theory ε} e (Th : Theoryᴴ η) (T′ : Theory ε′)
  → (sub : T ≪ T′)
  → Correctᴴ Th T e
    --------------------------------------
  → Correctᴴ Th T′ (weaken (sub .≲-eff) e)
weaken-correct e Th T′ sub C e′ ⦃ ζ ⦄ px = ≈-weaken sub _ _ (C e′ ⦃ ζ′ ⦄ px) 
  where ζ′ : e ⊑ e′
        ≲-eff ζ′ = ≲-trans (sub .≲-eff) (ζ .≲-eff)
        ≲-effᴴ ζ′ = ζ .≲-effᴴ
        preserves-cases ζ′ m e′′ = (ζ .preserves-cases m e′′)

compose-elab-correct :
  ∀ (e₁ : Elaboration η₁ ε₁)
  → (e₂ : Elaboration η₂ ε₂)
  → (T₁ : Theory ε₁)
  → (T₂ : Theory ε₂) 
  → (Th₁ : Theoryᴴ η₁)
  → (Th₂ : Theoryᴴ η₂) 
  → Correctᴴ Th₁ T₁ e₁
  → Correctᴴ Th₂ T₂ e₂
  → (σ : ε₁ ∙ ε₂ ≈ ε)
    -----------------------------------------------------------------------------------------
  → Correctᴴ (Th₁ [⊎]ᴴ Th₂) (compose-theory (T₁ ✴⟨ σ ⟩ T₂)) (compose-elab (e₁ ✴⟨ σ ⟩ e₂))
compose-elab-correct e₁ e₂ T₁ T₂ Th₁ Th₂ C₁ C₂ σ =
  [⊎]ᴴ-correct (compose-theory (T₁ ✴⟨ σ ⟩ T₂)) 
    (weaken-correct e₁ Th₁ (compose-theory (T₁ ✴⟨ σ ⟩ T₂)) (≪-compose-left T₁ T₂ σ) C₁)
    (weaken-correct e₂ Th₂ (compose-theory (T₁ ✴⟨ σ ⟩ T₂)) (≪-compose-right T₁ T₂ σ) C₂)

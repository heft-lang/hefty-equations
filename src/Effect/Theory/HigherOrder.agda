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
record Theoryᴴ (η : Effectᴴ) : Set₁ where
  no-eta-equality
  constructor ∥_∥ᴴ
  field
    equationsᴴ : List (Equationᴴ η) 

open Theoryᴴ public

record ExtensibleTheoryᴴ (η : Effectᴴ)  : Set₁ where
  field
    theoryᴴ : □ Theoryᴴ η 

open ExtensibleTheoryᴴ public 

variable Th Th₁ Th₂ Th₃ Th′ : Theoryᴴ η

-- A predicate asserting that a given equation is part of a theory
_◃ᴴ_ : Equationᴴ η → Theoryᴴ η → Set₁
eq ◃ᴴ Th = eq ∈ Th .equationsᴴ


-- Theory inclusion for higher-order theories
_⊆ᴴ_ : Theoryᴴ η → Theoryᴴ η → Set₁
Th₁ ⊆ᴴ Th₂ = {eq : Equationᴴ _} → eq ◃ᴴ Th₁ → eq ◃ᴴ Th₂

wk-theoryᴴ : η₁ ≲ η₂ → Theoryᴴ η₁ → Theoryᴴ η₂ 
wk-theoryᴴ i Th = ∥ map (wk-equationᴴ ⦃ i ⦄) (Th .equationsᴴ) ∥ᴴ

wk-ext-theoryᴴ : η₁ ≲ η₂ → ExtensibleTheoryᴴ η₁ → ExtensibleTheoryᴴ η₂
theoryᴴ (wk-ext-theoryᴴ i Th) = necessary λ i′ → □⟨ Th .theoryᴴ ⟩ ≲ᴴ-trans i i′

-- Coproduct of higher-order effect theories
_⟨+⟩ᴴ_ : ∀[ Theoryᴴ ⇒ Theoryᴴ ⇒ Theoryᴴ ]
(Th₁ ⟨+⟩ᴴ Th₂) .equationsᴴ = Th₁ .equationsᴴ ++ Th₂ .equationsᴴ

_⟨⊎⟩ᴴ_ : ∀[ ExtensibleTheoryᴴ ⇒ ExtensibleTheoryᴴ ⇒ ExtensibleTheoryᴴ ]
theoryᴴ (Th₁ ⟨⊎⟩ᴴ Th₂) = necessary λ i →
  (□⟨ Th₁ .theoryᴴ ⟩ i) ⟨+⟩ᴴ (□⟨ Th₂ .theoryᴴ ⟩ i)

_[+]ᴴ_ : Theoryᴴ η₁ → Theoryᴴ η₂ → Theoryᴴ (η₁ ·⊕ η₂)
Th₁ [+]ᴴ Th₂ = wk-theoryᴴ ·⊑-⊕-left Th₁ ⟨+⟩ᴴ wk-theoryᴴ ·⊑-⊕-right Th₂

_[⊎]ᴴ_ : ExtensibleTheoryᴴ η₁ → ExtensibleTheoryᴴ η₂ → ExtensibleTheoryᴴ (η₁ ·⊕ η₂)
Th₁ [⊎]ᴴ Th₂ = wk-ext-theoryᴴ ·⊑-⊕-left Th₁ ⟨⊎⟩ᴴ wk-ext-theoryᴴ ·⊑-⊕-right Th₂

-- Syntactic equivalence of programs with higher order effects, with respect to
-- a given theory `Th`. Analagous to how we defined syntactic equivalence for
-- first-order effect trees
infix 2 _≅⟨_⟩_
data _≅⟨_⟩_ {ε} {ξ} : (m₁ : Hefty (ξ ε) A) → Theoryᴴ ξ → (m₂ : Hefty (ξ ε) A) → Set₁ where

  ≅-refl  : ------------
            m ≅⟨ Th ⟩ m

  ≅-sym   : m₁ ≅⟨ Th ⟩ m₂
            -------------
          → m₂ ≅⟨ Th ⟩ m₁

  ≅-trans : m₁ ≅⟨ Th ⟩ m₂
          → m₂ ≅⟨ Th ⟩ m₃
            -------------
          → m₁ ≅⟨ Th ⟩ m₃

  ≅-cong  : (c : ξ ε .command)
          → (r₁ r₂ : ξ ε .response c → Hefty (ξ ε) A)
          → (s₁ s₂ : (ψ : ξ ε .fork c) → Hefty (ξ ε) (ξ ε .returns ψ))
          → (∀ {x} → r₁ x ≅⟨ Th ⟩ r₂ x)
          → (∀ {ψ} → s₁ ψ ≅⟨ Th ⟩ s₂ ψ)  
            -----------------------------------------------------
          → impure ⟪ c , r₁ , s₁ ⟫ ≅⟨ Th ⟩ impure ⟪ c , r₂ , s₂ ⟫

  ≅-eq    : (eq : Equationᴴ ξ)
          → eq ◃ᴴ Th
          → (δ : TypeContext (eq .Δ′))
          → (γ : eq .Γ′ ε δ)
          → (k : eq .R′ ε δ → Hefty (ξ ε) B)
            -----------------------------------------------
          → eq .rhsᴴ δ γ >>= k ≅⟨ Th ⟩ (eq .rhsᴴ δ γ >>= k)          

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
Correctᴴ : Theoryᴴ η  → ExtensibleTheory ε → Elaboration η ε → Set₁ 
Correctᴴ {ε = ε} Th T e =
  ∀ {eq : Equationᴴ _}
  → eq ◃ᴴ Th
  → {ε′ : Effect}
  → ⦃ i : ε ≲ ε′ ⦄
    -----------------------------------------
  → Respectsᴴ (_≈[ T ]_) (□⟨ e .elab ⟩ i) eq  

□-Correctᴴ : ExtensibleTheoryᴴ η → ExtensibleTheory ε → Elaboration η ε → Set₁
□-Correctᴴ {η = η} {ε} Th T e =
  ∀ {η′}
  → (e′ : Elaboration η′ ε)
  → ⦃ ζ : e ⊑ e′ ⦄
    -----------------------------------------
  → Correctᴴ (□⟨ Th .theoryᴴ ⟩ ζ .≲-eff) T e′

-- Equations that occur in a composed theory can be found in either of the
-- argument theories
[+]ᴴ-injective : ∀ Th₁ Th₂ {eq : Equationᴴ (η₁ ·⊕ η₂)}
         → eq ◃ᴴ (Th₁ [+]ᴴ Th₂)
         →   (eq ◃ᴴ wk-theoryᴴ ·⊑-⊕-left  Th₁ )
           ⊎ (eq ◃ᴴ wk-theoryᴴ ·⊑-⊕-right Th₂ )
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
◃ᴴ-weaken-lemma : ∀ Th (i : η₁ ≲ η₂)
       → (eq : Equationᴴ η₂)
       → eq ◃ᴴ wk-theoryᴴ i Th
       → ∃ λ (eq′ : Equationᴴ η₁) → eq′ ◃ᴴ Th × eq ≡ wk-equationᴴ ⦃ i ⦄ eq′
◃ᴴ-weaken-lemma Th w eq px with Th .equationsᴴ
... | eq′ ∷ eqs =
  case px of
    λ where (here refl) → _ , here refl , refl
            (there px′) →
              case ◃ᴴ-weaken-lemma (λ where .equationsᴴ → eqs) w eq px′ of
                λ where (a , px′′ , refl) → a , there px′′ , refl 

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
[+]ᴴ-correct
  : ∀ {e₁ e₂}
    → (T : ExtensibleTheory ε)
    → Correctᴴ Th₁ T e₁
    → Correctᴴ Th₂ T e₂
      -------------------------------------
    → Correctᴴ (Th₁ [+]ᴴ Th₂) T (e₁ ⟪⊕⟫ e₂)
[+]ᴴ-correct {Th₁ = Th₁} {Th₂ = Th₂} {e₁ = e₁} {e₂ = e₂} T C₁ C₂ px
  with [+]ᴴ-injective Th₁ Th₂ px
[+]ᴴ-correct {Th₁ = Th₁} {Th₂ = Th₂} {e₁ = e₁} {e₂ = e₂} T C₁ C₂ px
  | inj₁ px′ with ◃ᴴ-weaken-lemma Th₁ ·⊑-⊕-left _ px′
... | eq′ , px′′ , refl =
  begin
    fold-hefty pure ((□⟨ e₁ .elab ⟩ _) ⟨⊕⟩ (□⟨ e₂ .elab ⟩ _))
      (fold-hefty pure (injectᴴ ⦃ ⊑-⊕-left ⦄) (eq′ .lhsᴴ _ _))
  ≈⟪ ≡-to-≈ $ sym $ ⟨⊕⟩-fold-left (eq′ .lhsᴴ _ _) ⟫
    fold-hefty pure (□⟨ e₁ .elab ⟩ _) (eq′ .lhsᴴ _ _)
  ≈⟪ C₁ px′′  ⟫
    fold-hefty pure (□⟨ e₁ .elab ⟩ _) (eq′ .rhsᴴ _ _) 
  ≈⟪ ≡-to-≈ $ ⟨⊕⟩-fold-left (eq′ .rhsᴴ _ _) ⟫ 
    fold-hefty pure ((□⟨ e₁ .elab ⟩ _) ⟨⊕⟩ (□⟨ e₂ .elab ⟩ _))
      (fold-hefty pure (injectᴴ ⦃ ⊑-⊕-left ⦄) (eq′ .rhsᴴ _ _))
  ∎
  where
    open ≈-Reasoning (□⟨ T .theory ⟩ _) 
[+]ᴴ-correct {Th₁ = Th₁} {Th₂ = Th₂} {e₁ = e₁} {e₂ = e₂} T C₁ C₂ px
  | inj₂ px′ with ◃ᴴ-weaken-lemma Th₂ ·⊑-⊕-right _ px′
... | eq′ , px′′ , refl =
  begin
    fold-hefty pure ((□⟨ e₁ .elab ⟩ _) ⟨⊕⟩ (□⟨ e₂ .elab ⟩ _))
      (fold-hefty pure (injectᴴ ⦃ ⊑-⊕-right ⦄) (eq′ .lhsᴴ _ _))
  ≈⟪ ≡-to-≈ $ sym $ ⟨⊕⟩-fold-right (eq′ .lhsᴴ _ _) ⟫
    fold-hefty pure (□⟨ e₂ .elab ⟩ _) (eq′ .lhsᴴ _ _)
  ≈⟪ C₂ px′′ ⟫
    fold-hefty pure (□⟨ e₂ .elab ⟩ _) (eq′ .rhsᴴ _ _) 
  ≈⟪ ≡-to-≈ $ ⟨⊕⟩-fold-right (eq′ .rhsᴴ _ _) ⟫ 
    fold-hefty pure ((□⟨ e₁ .elab ⟩ _) ⟨⊕⟩ (□⟨ e₂ .elab ⟩ _))
      (fold-hefty pure (injectᴴ ⦃ ⊑-⊕-right ⦄) (eq′ .rhsᴴ _ _))
  ∎
  where open ≈-Reasoning _  

weaken-correct :
  ∀ {T : ExtensibleTheory ε} e (Th : Theoryᴴ η) (T′ : ExtensibleTheory ε′)
  → (sub : T ≪ T′)
  → Correctᴴ Th T e
    ---------------------------
  → Correctᴴ Th T′ (weaken (sub .inc) e)
weaken-correct e Th T′ sub₁ C px ⦃ i′ ⦄
  = ≈-weaken sub₁ ⦃ i′ ⦄ _ _ (C px ⦃ ≲-trans (sub₁ .inc) i′ ⦄)

compose-elab-correct :
  ∀ (e₁ : Elaboration η₁ ε₁)
  → (e₂ : Elaboration η₂ ε₂)
  → (T₁ : ExtensibleTheory ε₁)
  → (T₂ : ExtensibleTheory ε₂) 
  → (Th₁ : Theoryᴴ η₁)
  → (Th₂ : Theoryᴴ η₂) 
  → Correctᴴ Th₁ T₁ e₁
  → Correctᴴ Th₂ T₂ e₂
  → (σ : ε₁ ∙ ε₂ ≈ ε)
    -----------------------------------------------------------------------------------------
  → Correctᴴ (Th₁ [+]ᴴ Th₂) (compose-ext-theory (T₁ ✴⟨ σ ⟩ T₂)) (compose-elab (e₁ ✴⟨ σ ⟩ e₂))
compose-elab-correct e₁ e₂ T₁ T₂ Th₁ Th₂ C₁ C₂ σ =
  [+]ᴴ-correct
    {Th₁ = Th₁} {Th₂ = Th₂}
    {e₁ = weaken (≲-∙-left σ) e₁}
    {e₂ = weaken (≲-∙-right σ) e₂}
    (compose-ext-theory (T₁ ✴⟨ σ ⟩ T₂))
    (weaken-correct e₁ Th₁ (compose-ext-theory (T₁ ✴⟨ σ ⟩ T₂)) (≪-compose-left T₁ T₂ σ) C₁)
    (weaken-correct e₂ Th₂ (compose-ext-theory (T₁ ✴⟨ σ ⟩ T₂)) (≪-compose-right T₁ T₂ σ) C₂)


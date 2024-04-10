{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Functor.Monad

open import Core.Signature
open import Core.Extensionality
open import Core.MonotonePredicate 

open import Effect.Base
open import Effect.Theory.FirstOrder
open import Effect.Elaborate
open import Effect.Separation
open import Effect.Logic
open import Effect.Inclusion

open import Effect.Syntax.Free
open import Effect.Syntax.Hefty

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

open Connectives

--
-- TODO: this notion of equation seems to be too weak!!!!!!
-- 
record Equationᴴ (ξ : Effect → Effectᴴ) : Set₁ where
  constructor _≗ᴴ_
  field
    {Δ′}      : ℕ
    {Γ′ R′}   : Effect → TypeContext Δ′ → Set 
    lhsᴴ rhsᴴ : {ε : Effect} → Π[ Γ′ ε ⇒ R′ ε ⊢ Hefty (ξ ε) ]

open Equationᴴ public

embed-equation : Equation ε → Equationᴴ (const $ ↑ ε)
embed-equation eq = (embed-free ∘₂ eq .lhs) ≗ᴴ (embed-free ∘₂ eq .lhs)

-- Weakening of equations (for higher-order effects). That is, `Equationᴴ`
-- defines a functor over the category of h.o. effects
wk-equationᴴ : ⦃ ∀ {ε} → ξ₁ ε ⊑ ξ₂ ε ⦄ → Equationᴴ ξ₁ → Equationᴴ ξ₂ 
wk-equationᴴ eq = (♯ᴴ ∘₂ eq .lhsᴴ) ≗ᴴ (♯ᴴ ∘₂ eq .rhsᴴ) 


-- Again, an algebra respects an equation if folding lhs and rhs gives the same
-- result, where "sameness" is with respect a given binary relation that is kept
-- abstract here.
-- 
-- We opt for this generalization (rather than using propositional equality)
-- here, because later we define correctness of elaborations as
Respectsᴴ : (_~_ : ∀ {A} → Free ε A → Free ε A → Set₁) → Algebra (ξ ε) (Free ε) → Equationᴴ ξ → Set₁
Respectsᴴ _~_ alg (lhs ≗ᴴ rhs) =
  ∀ {δ γ} → fold-hefty pure alg (lhs δ γ) ~ fold-hefty pure alg (rhs δ γ)

-- Theories of higher-order effects are collections of equations
record Theoryᴴ (ξ : Effect → Effectᴴ) : Set₁ where
  no-eta-equality
  constructor ∥_∥ᴴ
  field
    equationsᴴ : List (Equationᴴ ξ) 

open Theoryᴴ public


variable Th Th₁ Th₂ Th₃ Th′ : Theoryᴴ ξ 

-- A predicate asserting that a given equation is part of a theory
_◃ᴴ_ : Equationᴴ ξ → Theoryᴴ ξ → Set₁
eq ◃ᴴ Th = eq ∈ Th .equationsᴴ

-- Theory inclusion for higher-order theories
_⊆ᴴ_ : Theoryᴴ ξ → Theoryᴴ ξ → Set₁
Th₁ ⊆ᴴ Th₂ = {eq : Equationᴴ _} → eq ◃ᴴ Th₁ → eq ◃ᴴ Th₂

embed-theory : Theory ε → Theoryᴴ (const $ ↑ ε)
embed-theory T .equationsᴴ = map embed-equation (map □-extract $ T .equations)

wk-theoryᴴ : ⦃ ∀ {ε} → ξ₁ ε ⊑ ξ₂ ε ⦄ → Theoryᴴ ξ₁ → Theoryᴴ ξ₂ 
wk-theoryᴴ eq = ∥ map wk-equationᴴ (eq .equationsᴴ) ∥ᴴ

-- Coproduct of higher-order effect theories
_⟨+⟩ᴴ_ : ∀[ Theoryᴴ ⇒ Theoryᴴ ⇒ Theoryᴴ ]
(Th₁ ⟨+⟩ᴴ Th₂) .equationsᴴ = Th₁ .equationsᴴ ++ Th₂ .equationsᴴ

_[+]ᴴ_ : Theoryᴴ ξ₁ → Theoryᴴ ξ₂ → Theoryᴴ (ξ₁ ·⊕ ξ₂)
Th₁ [+]ᴴ Th₂ = wk-theoryᴴ ⦃ ⊑-⊕-left ⦄ Th₁ ⟨+⟩ᴴ wk-theoryᴴ ⦃ ⊑-⊕-right ⦄ Th₂

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
Correctᴴ : Theoryᴴ ξ → Theory ε → Elaboration ξ ε → Set₁ 
Correctᴴ Th T e =
  ∀ {eq : Equationᴴ _}
  → eq ◃ᴴ Th
  → ∀ {ε′} 
  → (T′ : Theory ε′) → (sub : T ≪ T′) 
  → Respectsᴴ (_≈⟨ T′ ⟩_) (□⟨ e .elab ⟩ sub .inc) eq 

-- Equations that occur in a composed theory can be found in either of the
-- argument theories
[+]ᴴ-injective : ∀ Th₁ Th₂ {eq : Equationᴴ (ξ₁ ·⊕ ξ₂)}
         → eq ◃ᴴ (Th₁ [+]ᴴ Th₂)
         →   (eq ◃ᴴ wk-theoryᴴ ⦃ ⊑-⊕-left  ⦄ Th₁ )
           ⊎ (eq ◃ᴴ wk-theoryᴴ ⦃ ⊑-⊕-right ⦄ Th₂ )
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
◃ᴴ-weaken-lemma : ∀ Th (w : ∀ {ε} → ξ₁ ε ⊑ ξ₂ ε)
       → (eq : Equationᴴ ξ₂)
       → eq ◃ᴴ wk-theoryᴴ ⦃ w ⦄ Th
       → ∃ λ (eq′ : Equationᴴ ξ₁) → eq′ ◃ᴴ Th × eq ≡ wk-equationᴴ ⦃ w ⦄ eq′ 
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
                  ≡ fold-hefty k (f ⟨⊕⟩ g) (♯ᴴ ⦃ ⊑-⊕-left ⦄ m)
⟨⊕⟩-fold-left (pure _)                           = refl
⟨⊕⟩-fold-left (impure ⟪ c , r , s ⟫) {f} {g} {k} =
  cong₂
    (λ □₁ □₂ → f .α ⟪ c , □₁ , □₂ ⟫)
    ( extensionality λ x → ⟨⊕⟩-fold-left $ r x )
    ( extensionality λ x → ⟨⊕⟩-fold-left $ s x )

⟨⊕⟩-fold-right : ∀ (m : Hefty η A)
                  {f : Algebra η′ F} {g : Algebra η F}
                  {k : ∀[ id ⇒ F ]}
                →   fold-hefty k g m
                  ≡ fold-hefty k (f ⟨⊕⟩ g) (♯ᴴ ⦃ ⊑-⊕-right ⦄ m)
⟨⊕⟩-fold-right (pure _)                           = refl
⟨⊕⟩-fold-right (impure ⟪ c , r , s ⟫) {f} {g} {k} =
  cong₂
    (λ □₁ □₂ → g .α ⟪ c , □₁ , □₂ ⟫)
    ( extensionality λ x → ⟨⊕⟩-fold-right $ r x )
    ( extensionality λ x → ⟨⊕⟩-fold-right $ s x )
    


module _ {T : Theory ε} where

  -- "Homogeneous" composition of correctness proofs for h.o. effect theories.
  --
  -- This theorem establishes that correctness of composed elaborations follows
  -- from correctness of their components, provided they assume the same lower
  -- bound on the algebraic effects for elaboration, and establish correctness
  -- w.r.t. the same first-order effect theory.
  ⟪⊕⟫-correct
    : ∀ {e₁ e₂} 
      → Correctᴴ Th₁ T e₁
      → Correctᴴ Th₂ T e₂
        -------------------------------------
      → Correctᴴ (Th₁ [+]ᴴ Th₂) T (e₁ ⟪⊕⟫ e₂)

  ⟪⊕⟫-correct {Th₁ = Th₁} {Th₂ = Th₂} {e₁ = e₁} {e₂ = e₂} c₁ c₂ px T′ it
    with [+]ᴴ-injective Th₁ Th₂ px
  ⟪⊕⟫-correct {Th₁ = Th₁} {Th₂ = Th₂} {e₁ = e₁} {e₂ = e₂} c₁ c₂ px T′ it
    | inj₁ px′ with ◃ᴴ-weaken-lemma Th₁ ⊑-⊕-left _ px′
  ... | eq′ , px′′ , refl = begin
      fold-hefty pure ((□⟨ e₁ .elab ⟩ it .inc) ⟨⊕⟩ (□⟨ e₂ .elab ⟩ it .inc))
        (fold-hefty pure (injectᴴ ⦃ ⊑-⊕-left ⦄) (eq′ .lhsᴴ _ _))
    ≈⟪ ≡-to-≈ $ sym $ ⟨⊕⟩-fold-left (eq′ .lhsᴴ _ _) ⟫
      fold-hefty pure (□⟨ e₁ .elab ⟩ it .inc) (eq′ .lhsᴴ _ _)
    ≈⟪ c₁ px′′ T′ it ⟫
      fold-hefty pure (□⟨ e₁ .elab ⟩ it .inc) (eq′ .rhsᴴ _ _) 
    ≈⟪ ≡-to-≈ $ ⟨⊕⟩-fold-left (eq′ .rhsᴴ _ _) ⟫ 
      fold-hefty pure ((□⟨ e₁ .elab ⟩ it .inc) ⟨⊕⟩ (□⟨ e₂ .elab ⟩ it .inc))
        (fold-hefty pure (injectᴴ ⦃ ⊑-⊕-left ⦄) (eq′ .rhsᴴ _ _))
    ∎
    where open ≈-Reasoning T′
  ⟪⊕⟫-correct {Th₁ = Th₁} {Th₂ = Th₂} {e₁ = e₁} {e₂ = e₂} c₁ c₂ px T′ it
    | inj₂ px′ with ◃ᴴ-weaken-lemma Th₂ ⊑-⊕-right _ px′
  ... | eq′ , px′′ , refl = begin
      fold-hefty pure ((□⟨ e₁ .elab ⟩ it .inc) ⟨⊕⟩ (□⟨ e₂ .elab ⟩ it .inc))
        (fold-hefty pure (injectᴴ ⦃ ⊑-⊕-right ⦄) (eq′ .lhsᴴ _ _))
    ≈⟪ ≡-to-≈ $ sym $ ⟨⊕⟩-fold-right (eq′ .lhsᴴ _ _) ⟫
      fold-hefty pure (□⟨ e₂ .elab ⟩ it .inc) (eq′ .lhsᴴ _ _)
    ≈⟪ c₂ px′′ T′ it ⟫ 
      fold-hefty pure (□⟨ e₂ .elab ⟩ it .inc) (eq′ .rhsᴴ _ _) 
    ≈⟪ ≡-to-≈ $ ⟨⊕⟩-fold-right (eq′ .rhsᴴ _ _) ⟫
      fold-hefty pure ((□⟨ e₁ .elab ⟩ it .inc) ⟨⊕⟩ (□⟨ e₂ .elab ⟩ it .inc))
        (fold-hefty pure (injectᴴ ⦃ ⊑-⊕-right ⦄) (eq′ .rhsᴴ _ _))
    ∎
    where open ≈-Reasoning T′ 


weaken-correct :
  ∀ {T : Theory ε} e (Th : Theoryᴴ ξ) (T′ : Theory ε′)
  → (sub : T ≪ T′)
  → Correctᴴ Th T e
    ---------------------------
  → Correctᴴ Th T′ (weaken (sub .inc) e)
weaken-correct e Th T′ sub₁ c px T′′ sub₂
  = c px  T′′ $ ≪-trans sub₁ sub₂ 


compose-elab-correct
  : ∀ (e₁ : Elaboration ξ₁ ε₁) (e₂ : Elaboration ξ₂ ε₂)
    → Correctᴴ Th₁ T₁ e₁
    → Correctᴴ Th₂ T₂ e₂
    → (σ : ε₁ ∙ ε₂ ≈ ε)
      -------------------------------------------------------------------------------------
    → Correctᴴ (Th₁ [+]ᴴ Th₂) (compose-theory (T₁ ✴⟨ σ ⟩ T₂)) (compose-elab (e₁ ✴⟨ σ ⟩ e₂))
    
compose-elab-correct {Th₁ = Th₁} {T₁ = T₁} {Th₂} {T₂ = T₂} e₁ e₂ c₁ c₂ σ =
  ⟪⊕⟫-correct
    {T = compose-theory (T₁ ✴⟨ σ ⟩ T₂)} {Th₁ = Th₁} {Th₂ = Th₂}
    {e₁ = weaken (≲-∙-left σ) e₁}
    {e₂ = weaken (≲-∙-right σ) e₂}
    ( weaken-correct {T = T₁} e₁ Th₁
        ( compose-theory (T₁ ✴⟨ σ ⟩ T₂) )
        ( ≪-compose-left  T₁ T₂ σ )
      c₁ )
    ( weaken-correct {T = T₂} e₂ Th₂
        ( compose-theory (T₁ ✴⟨ σ ⟩ T₂) )
        ( ≪-compose-right T₁ T₂ σ)
      c₂ ) 


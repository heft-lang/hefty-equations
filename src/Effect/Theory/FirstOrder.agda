open import Effect.Base
open import Effect.Separation
open import Effect.Handle
open import Effect.Logic

open import Free.Base

open import Core.Functor
open import Core.Container
open import Core.MonotonePredicate Effect _≲_
open import Core.DisjointUnion
open import Core.Extensionality

open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any hiding (map)

open import Data.Nat
open import Data.Vec hiding (map ; _++_)
open import Data.Maybe using (Maybe ; just ; nothing ; maybe′)

open import Relation.Unary hiding (_∈_ ; _⊆_)
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open import Data.Empty

open import Function
open import Function.Construct.Symmetry
open import Function.Construct.Composition
open import Level

{- Most stuff in this module is adapted from "Reasoning about Effect Interaction
   by Fusion, Zhixuan Yang and Nicholas Wu" -}
module Effect.Theory.FirstOrder where

open Connectives

variable c c₁ c₂ c₃ : Free ε A

-- We define type contexts as a product by induction over the length rather than
-- a vector, because this gives us some η-equalities that come in handy when
-- defining effect theories since they save us from having to pattern match on
-- the type context in order to make the goal type of the lhs and rhs of
-- equations compute.
TypeContext : ℕ → Set₁
TypeContext zero    = Lift _ ⊤
TypeContext (suc n) = Set × TypeContext n

-- Equations, packaged together with their context 
record Equation (ε : Effect) : Set₁ where
  constructor _≗_ 
  field
    {Δ′}    : ℕ
    {Γ′ R′} : TypeContext Δ′ → Set
    lhs rhs : Π[ Γ′ ⇒ R′ ⊢ Free ε ] 
  
open Equation public 

variable Δ Δ₁ Δ₂ : ℕ 
         Γ Γ₁ Γ₂ R : Vec Set Δ → Set 

instance eq-monotone : Monotone Equation
eq-monotone .weaken i eq = (♯ ⦃ i ⦄ ∘₂ eq .lhs) ≗ (♯ ⦃ i ⦄ ∘₂ eq .rhs) 

-- Equations are functors over the category of containers and container morphisms 
hmap-eq : ε₁ ↦ ε₂ → Equation ε₁ → Equation ε₂
hmap-eq θ eq = (hmap-free θ ∘₂ eq .lhs) ≗ (hmap-free θ ∘₂ eq .rhs)

-- We can re-brand equations over a given effect to equations for a different
-- but equivalent effect
eq-resp-≋ : ε₁ ≋ ε₂ → Equation ε₁ → Equation ε₂
eq-resp-≋ eqv = hmap-eq (eqv .iso _ .Inverse.to) 

-- We say that an algebra "respects" an equation if folding with that algebra
-- over both the left- and right-hand-side of the equation produces equal results
Respects : Algebraᶜ ε A → □ Equation ε → Set₁
Respects alg eq =
  ∀ {δ γ k} → fold-free k alg (□-extract eq .lhs δ γ) ≡ fold-free k alg (□-extract eq .rhs δ γ) 

-- A theory of an effect `ε` is simply a collection of equations
record Theory (ε : Effect) : Set₁ where
  no-eta-equality
  constructor ∥_∥
  field
    equations : List (□ Equation ε)


open Theory public

-- A predicate asserting that a given equation is part of a theory
_◃_ : □ Equation ε → Theory ε → Set₁
eq ◃ T = eq ∈ T .equations

-- Theory inclusion
_⊆_ : Theory ε → Theory ε → Set₁
T₁ ⊆ T₂ = ∀ {eq} → eq ◃ T₁ → eq ◃ T₂ 

-- Effect theories are monotone predicates over effects 
instance theory-monotone : Monotone Theory
theory-monotone .weaken i T = ∥ (map (weaken i) $ T .equations) ∥ 

theory-resp-≋ : ε₁ ≋ ε₂ → Theory ε₁ → Theory ε₂ 
theory-resp-≋ eqv T = ∥ map (□-resp-≋ eqv) $ T .equations ∥

◃-weaken : {eq : □ Equation ε} → ∀ T → eq ◃ T → (i : ε ≲ ε′) → weaken i eq ◃ weaken i T
◃-weaken T px i with T .equations
◃-weaken T (here refl) _ | _ ∷ _  = here refl
◃-weaken T (there px)  i | _ ∷ xs = there (◃-weaken ∥ xs ∥ px i)

postulate ◃-inv : {eq : □ Equation ε₂} → ∀ T → (i : ε₁ ≲ ε₂) → eq ◃ weaken i T → ∃ λ eq′ → eq′ ◃ T × weaken i eq′ ≡ eq

-- Heterogeneous theory inclusion
module _ where

  -- Use a record to help type inference 
  record _⊆⟨_⟩_ (T₁ : Theory ε₁) (i : ε₁ ≲ ε₂) (T₂ : Theory ε₂) : Set₁ where 
    field sub : ∀ {eq} → eq ◃ T₁ → weaken i eq ◃ T₂ 

  open _⊆⟨_⟩_ public 

  -- The following two lemmas witness that heterogeneous theory inclusion
  -- carries the structure of what we might refer to as a "graded preorder" (or,
  -- monoid) The grading is given by effect inclusion witnesses, which form a
  -- monoid with reflexivity and transitivity as respectively the unit and
  -- multiplication of the monoid.
  --
  -- TODO: is this a known structure? 

  postulate ⟨⊆⟩-refl : {T : Theory ε} → T ⊆⟨ ≲-refl ⟩ T
-- ⟨⊆⟩-refl {T = T} {eq = eq} px with T .equations
-- ⟨⊆⟩-refl {T = T} {eq = .eq} (here refl) | eq ∷ _ = here (
--   begin
--     necessary (λ i → □⟨ eq ⟩ ≲-trans ≲-refl i)
--   ≡⟨ {! !} ⟩
--     necessary (λ i → □⟨ eq ⟩ i) 
--   ≡⟨⟩ {- η-equivalence for □ modality -} 
--     eq
--   ∎ )
--   where open ≡-Reasoning
-- ⟨⊆⟩-refl {T = T} {eq = eq} (there px) | _ ∷ xs = there (⟨⊆⟩-refl {T = ∥ xs ∥} px)
--
  postulate 
    ⟨⊆⟩-trans :
      ∀ {T₁ : Theory ε₁} {T₂ : Theory ε₂} {T : Theory ε}
        {i₁ : ε₁ ≲ ε₂} {i₂ : ε₂ ≲ ε}
      → T₁ ⊆⟨ i₁ ⟩ T₂ → T₂ ⊆⟨ i₂ ⟩ T
        ----------------------------
      → T₁ ⊆⟨ ≲-trans i₁ i₂ ⟩ T
-- ⟨⊆⟩-trans {T₁ = T₁} {T₂ = T₂} {T = T} {i₁ = i₁} {i₂} sub₁ sub₂ {eq} px =
--   subst (λ ○ → ○ ◃ T) (
--     begin
--       (necessary λ i′ → □⟨ eq ⟩ ≲-trans i₁ (≲-trans i₂ i′))
--     ≡⟨ {!!} ⟩
--       (necessary λ i′ → □⟨ eq ⟩ ≲-trans (≲-trans i₁ i₂) i′)
--     ∎ ) (sub₂ (sub₁ px))
--   where open ≡-Reasoning
--

  -- We can't quite complete the proofs above yet. To do so, we would need to
  -- assert that weakening of equations respects the monoidal structure of
  -- effect inclusion in a suitable sense. What does this mean, precisely? Given
  -- two witnesses i₁ and i₂ that can be "equated" under the monoid laws (with
  -- reflexivity as the unit and transitivity as composition), weakening an
  -- equation with either witness should give the same result.
  --
  -- This begs the question of what it means for two witnesses to be
  -- equal. Propositional equality would be too strong, especially for the
  -- current semantic defintion of effect inclusion as it would require equality
  -- of the inverse proofs. This would require UIP to prove, but beyond that
  -- it's completely unecessary if we're only interested in knowing that
  -- inclusions give the same result once we compute the injections. A more
  -- appealing setup would be to require (extensional) equality of the transport
  -- witnesses.
  --
  -- Consequently, we would require additional proofs for all equations--which
  -- are defined as function spaces over inclusion witnesses--to respect this
  -- weaker notion of equality. Equations shouldn't really use this witness
  -- other than to pass it onto smart constructors, so if we can prove that
  -- weakening of effect trees respects extensional equality of inclusions
  -- (which it should), we should be good.


-- Coproduct of effect theories
_⟨+⟩_ : ∀[ Theory ⇒ Theory ⇒ Theory ]
(T₁ ⟨+⟩ T₂) .equations = T₁ .equations ++ T₂ .equations

-- Sum of effect theories
_[+]_ : Theory ε₁ → Theory ε₂ → Theory (ε₁ ⊕ᶜ ε₂) 
_[+]_ {ε₁} {ε₂} T₁ T₂ = weaken (≲-⊕ᶜ-left ε₂) T₁ ⟨+⟩ weaken (≲-⊕ᶜ-right ε₁) T₂

◃-⟨+⟩-left : ∀ {eq : □ Equation ε} → (T₁ T₂ : Theory ε) → eq ◃ T₁ → eq ◃ (T₁ ⟨+⟩ T₂)
◃-⟨+⟩-left T₁ T₂ px = ∈-++⁺ˡ px

◃-⟨+⟩-right : ∀ {eq : □ Equation ε} → (T₁ T₂ : Theory ε) → eq ◃ T₂ → eq ◃ (T₁ ⟨+⟩ T₂)
◃-⟨+⟩-right T₁ T₂ px = ∈-++⁺ʳ (T₁ .equations) px

-- "Heterogeneous" composition of effect theories" 
compose-theory : ∀[ (Theory ✴ Theory) ⇒ Theory ]
compose-theory (T₁ ✴⟨ σ ⟩ T₂) = weaken (≲-∙-left σ) T₁ ⟨+⟩ weaken (≲-∙-right σ) T₂


-- Heterogeneous theory inclusion respects heterogeneous composition in both positions
⟨⊆⟩-compose-left :
  ∀ (T₁ : Theory ε₁) (T₂ : Theory ε₂)
  → (σ : ε₁ ∙ ε₂ ≈ ε)
     -----------------------------------------------
  → T₁ ⊆⟨ ≲-∙-left σ ⟩ compose-theory (T₁ ✴⟨ σ ⟩ T₂)
  
⟨⊆⟩-compose-left T₁ T₂ σ .sub px =
  ◃-⟨+⟩-left
    (weaken (≲-∙-left σ) T₁)
    (weaken (≲-∙-right σ) T₂)
    (◃-weaken T₁ px (≲-∙-left σ))

⟨⊆⟩-compose-right :
  ∀ (T₁ : Theory ε₁) (T₂ : Theory ε₂)
  → (σ : ε₁ ∙ ε₂ ≈ ε)
    -------------------------------------------------
  → T₂ ⊆⟨ ≲-∙-right σ ⟩ compose-theory (T₁ ✴⟨ σ ⟩ T₂)

⟨⊆⟩-compose-right T₁ T₂ σ .sub px =
  ◃-⟨+⟩-right
    (weaken (≲-∙-left σ) T₁)
    (weaken (≲-∙-right σ) T₂)
    (◃-weaken T₂ px (≲-∙-right σ))


variable T T₁ T₂ T₃ T′ : Theory ε

-- The following data type defines syntactic equality of computations with
-- effects `ε` with respect to a given effect theory `T` of `ε`.
infix 2 _≈⟨_⟩_
data _≈⟨_⟩_ {ε} : (c₁ : Free ε A) → Theory ε → (c₂ : Free ε A) → Set₁ where

  ≈-refl  : ----------
            c ≈⟨ T ⟩ c

  ≈-sym   : c₁ ≈⟨ T ⟩ c₂
            -------
          → c₂ ≈⟨ T ⟩ c₁

  ≈-trans : c₁ ≈⟨ T ⟩ c₂
          → c₂ ≈⟨ T ⟩ c₃
            -----------------
          → c₁ ≈⟨ T ⟩ c₃

  ≈-cong  : (s : ε .shape)
          → (p₁ p₂ : ε .position s → Free ε A)
          → (∀ {x} → p₁ x ≈⟨ T ⟩ p₂ x)
            ------------------------------------------
          → impure ⟨ s , p₁ ⟩ ≈⟨ T ⟩ impure ⟨ s , p₂ ⟩   

  ≈-eq    : (eq : □ Equation ε)
          → (px : eq ◃ T)  
          → (δ  : TypeContext (□-extract eq .Δ′))
          → (γ  : □-extract eq .Γ′ δ)
          → (k  : R′ (□-extract eq) δ → Free ε A) 
            --------------------------------------------------------------
          → □-extract eq .lhs δ γ >>= k ≈⟨ T ⟩ □-extract eq .rhs δ γ >>= k
          

-- Propositional equality of effect trees can (clearly) be reflected as a
-- syntactic equivalence
≡-to-≈ : {c₁ c₂ : Free ε A} → c₁ ≡ c₂ → c₁ ≈⟨ T ⟩ c₂
≡-to-≈ refl = ≈-refl

{- Reflect the monad laws for Free as syntactic equivalences -}

>>=-idˡ-≈ : ∀ (k : A → Free ε B) x → return x >>= k ≈⟨ T ⟩ k x
>>=-idˡ-≈ k x = ≡-to-≈ (>>=-idˡ x k) 

>>=-idʳ-≈ : (m : Free ε A) → m >>= pure ≈⟨ T ⟩ m
>>=-idʳ-≈ m = ≡-to-≈ (>>=-idʳ m) 

>>=-assoc-≈ : ∀ {D : Set} (k₁ : A → Free ε B) (k₂ : B → Free ε D) (m : Free ε A)
             → flip (free-monad Monad.∗) (flip (free-monad Monad.∗) m k₁) k₂ ≈⟨ T ⟩ m >>= (k₁ >=> k₂)
>>=-assoc-≈ k₁ k₂ m = ≡-to-≈ (>>=-assoc k₁ k₂ m)
             

-- Below we define the key correctness property of handlers 
-- 
-- In the IFCP paper they sketch a proof that Correctness of a handler `h`
-- implies correctness of the transformation `handle h`. But this relies on
-- parametricty, so I'm sceptical we can recreate the same proof here.

-- Correctness of handlers: we say that a handler is correct with respect to a
-- given theory `T` of the effect it handlers iff it's algebra respects all
-- equations of `T`.
Correct : {P : Set} → Theory ε → Handler ε P F → Set₁
Correct T h =
  ∀ {A ε′}
  → {eq : □ Equation _}
  → eq ◃ T
    --------------------------------------
  → Respects (h .hdl {A = A} {ε′ = ε′}) eq 


-- Restricted version of adequacy that presupposes that the effect to be handled
-- is at the front of the tree's signature
Adequate′ : Handler ε₁ A F → Theory ε₁ → Set₁
Adequate′ {ε₁} {A} H T =
  ∀ {B ε₂} (x : A)
  → (m₁ m₂ : Free (ε₁ ⊕ᶜ ε₂) B)
  → ∀ {T′} 
  → weaken (≲-⊕ᶜ-left ε₂) T ⊆ T′ 
  → handle′ {ε₂ = ε₂} H x m₁ ≡ handle′ H x m₂
    -----------------------------------------
  → m₁ ≈⟨ T′ ⟩ m₂

-- Adequacy of a Handler w.r.t. a given theory of the effect it handles 
Adequate : Handler ε₁ A F → Theory ε₁ → Set₁
Adequate {ε₁} {A} H T =
  ∀ {B ε₂ ε} (x : A)
  → (m₁ m₂ : Free ε B)
  → (σ : ε₁ ∙ ε₂ ≈ ε)
  → ∀ {T′}
  → weaken (≲-∙-left σ) T ⊆ T′ 
  → handle H σ x m₁ ≡ handle H σ x m₂
    ---------------------------------
  → m₁ ≈⟨ T′ ⟩ m₂

open DisjointUnion

postulate sep-adequate : (H : Handler ε₁ A F) → Π[ Adequate′ H ⇒ Adequate H ]
-- sep-adequate {ε₁} H T adq {ε₂ = ε₂} {ε} a m₁ m₂ σ {T′} T⊆T′ eq
--   with adq a (separate σ m₁) (separate σ m₂) {T′ = T′′} {!!} eq 
--   where
--     eq′ : ε ≋ (ε₁ ⊕ᶜ ε₂) 
--     eq′ = (≋-sym (∙-to-≋ σ)) 
--   
--     T′′ : Theory (ε₁ ⊕ᶜ ε₂)
--     T′′ = theory-resp-≋ eq′ T′
-- 
-- ... | eqv = {!!} 
-- 
-- 

module ≈-Reasoning (T : Theory ε) where

  infix 3 _≈_
  _≈_ : Free ε A → Free ε A → Set₁
  c₁ ≈ c₂ = c₁ ≈⟨ T ⟩ c₂

  begin_ : {c₁ c₂ : Free ε A} → c₁ ≈ c₂ → c₁ ≈ c₂ 
  begin eq = eq 

  _∎ : (c : Free ε A) → c ≈ c
  c ∎ = ≈-refl

  _≈⟪⟫_ : (c₁ : Free ε A) {c₂ : Free ε A} → c₁ ≈ c₂ → c₁ ≈ c₂  
  c₁ ≈⟪⟫ eq = eq

  _≈⟪_⟫_  : (c₁ {c₂ c₃} : Free ε A) → c₁ ≈ c₂ → c₂ ≈ c₃ → c₁ ≈ c₃
  c₁ ≈⟪ eq₁ ⟫ eq₂ = ≈-trans eq₁ eq₂

  infix 1 begin_
  infixr 2 _≈⟪_⟫_ _≈⟪⟫_
  infix 3 _∎


-- Equivalence following from equations of the theory, specialized to empty continuations
≈-eq′ : (eq : □ Equation ε)
      → eq ◃ T → {δ : TypeContext (□-extract eq .Δ′)}
      → {γ : □-extract eq .Γ′ δ}
        --------------------------------------------------
      → □-extract eq .lhs δ γ ≈⟨ T ⟩ □-extract eq .rhs δ γ
      
≈-eq′ eq px {δ} {γ} =
  begin
    □-extract eq .lhs δ γ
  ≈⟪ ≈-sym (>>=-idʳ-≈ _) ⟫
    □-extract eq .lhs δ γ >>= pure
  ≈⟪ ≈-eq eq px δ γ pure ⟫
    □-extract eq .rhs δ γ >>= pure 
  ≈⟪ >>=-idʳ-≈ _ ⟫
    □-extract eq .rhs δ γ
  ∎ 
  where open ≈-Reasoning _


-- monadic bind respects syntactic equivalence of effect trees in the left position 
>>=-resp-≈ˡ : {m₁ m₂ : Free ε A} {k : A → Free ε B} → m₁ ≈⟨ T ⟩ m₂ → m₁ >>= k ≈⟨ T ⟩ m₂ >>= k
>>=-resp-≈ˡ ≈-refl                      = ≈-refl
>>=-resp-≈ˡ (≈-sym eq)                  = ≈-sym (>>=-resp-≈ˡ eq)
>>=-resp-≈ˡ (≈-trans eq₁ eq₂)           = ≈-trans (>>=-resp-≈ˡ eq₁) (>>=-resp-≈ˡ eq₂)
>>=-resp-≈ˡ {k = k} (≈-cong s p₁ p₂ x)  = ≈-cong s ((_>>= k) ∘ p₁) ((_>>= k) ∘ p₂) λ {v} → >>=-resp-≈ˡ (x {v})
>>=-resp-≈ˡ {k = k} (≈-eq eq px δ γ k′) =
  begin
    (□-extract eq .lhs δ γ >>= k′) >>= k
  ≈⟪ >>=-assoc-≈ k′ k (□-extract eq .lhs δ γ) ⟫
    □-extract eq .lhs δ γ >>= (k′ >=> k)
  ≈⟪ ≈-eq eq px δ γ (k′ >=> k) ⟫
    □-extract eq .rhs δ γ >>= (k′ >=> k)
  ≈⟪ ≈-sym (>>=-assoc-≈ k′ k (□-extract eq .rhs δ γ)) ⟫
    (□-extract eq .rhs δ γ >>= k′) >>= k 
  ∎
  where open ≈-Reasoning _


-- monadic bind respects syntactic equivalence of effect trees in the right position 
>>=-resp-≈ʳ : {k₁ k₂ : A → Free ε B} {m : Free ε A} → (∀ a → k₁ a ≈⟨ T ⟩ k₂ a) → m >>= k₁ ≈⟨ T ⟩ m >>= k₂ 
>>=-resp-≈ʳ {m = pure x} eq = eq _
>>=-resp-≈ʳ {k₁ = k₁} {k₂} {m = impure ⟨ c , r ⟩} eq =
  begin
    impure ⟨ c , r ⟩ >>= k₁
  ≈⟪⟫ {- Definition of >>= -} 
    impure ⟨ c , (_>>= k₁) ∘ r ⟩  
  ≈⟪ ≈-cong c ((_>>= k₁) ∘ r) ((_>>= k₂) ∘ r) (>>=-resp-≈ʳ {m = r _} eq) ⟫
    impure ⟨ c , (_>>= k₂) ∘ r ⟩  
  ≈⟪⟫ {- Definition of >>= -}  
    impure ⟨ c , r ⟩ >>= k₂
  ∎
  where open ≈-Reasoning _ 


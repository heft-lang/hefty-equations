open import Effect.Base
open import Effect.Separation
open import Effect.Handle
open import Effect.Logic

open import Free.Base

open import Core.Functor
open import Core.Container
open import Core.MonotonePredicate Effect _≲_
open import Core.DisjointUnion

open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit

open import Data.List
open import Data.List.Membership.Propositional
open import Data.Nat
open import Data.Vec hiding (map ; _++_)
open import Data.Maybe using (Maybe ; just ; nothing ; maybe′)

open import Relation.Unary hiding (_∈_ ; _⊆_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)
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

-- Heterogeneous theory inclusion
_∣⊆∣_ : Theory ε₁ → Theory ε₂ → Set₁
T₁ ∣⊆∣ T₂ = ∀ i → weaken i T₁ ⊆ T₂

-- Coproduct of effect theories
_⟨+⟩_ : ∀[ Theory ⇒ Theory ⇒ Theory ]
(T₁ ⟨+⟩ T₂) .equations = T₁ .equations ++ T₂ .equations

-- Sum of effect theories
_[+]_ : Theory ε₁ → Theory ε₂ → Theory (ε₁ ⊕ᶜ ε₂) 
_[+]_ {ε₁} {ε₂} T₁ T₂ = weaken (≲-⊕ᶜ-left ε₂) T₁ ⟨+⟩ weaken (≲-⊕ᶜ-right ε₁) T₂

-- -- 
-- -- -- Tensor of effect theories
-- -- record _⊗_ (T₁ : Theory ε₁) (T₂ : Theory ε₂) : Set₁ where
-- --   field
-- --     laws : {c₁ : ε₁ .shape} → {c₂ : ε₂ .shape} → {!!} 
-- -- 
-- --   theory : Theory (ε₁ ⊕ᶜ ε₂)
-- --   theory = T₁ [+] T₂ 
-- -- 

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
-- -- Correctness of transformations: we say that a handler `h` is a correct
-- -- transformation iff it is the case that equality of computations under a summed
-- -- effect theory `T₁ [+] T₂` implies equality under theory `T₂` after handling
-- -- `c₁` and `c₂` with `h`.
-- CorrectT : {P : Set} → Handler ε P F → Set₁
-- CorrectT {ε = ε} h =
--   ∀ {ε′}{c₁ c₂ : Free (ε ⊕ᶜ ε′) _}
--     {T₁ : Theory ε} {T₂ : Theory ε′} {v}
--   → c₁ ≈⟨ T₁ [+] T₂ ⟩ c₂ → handle h c₁ v ≈⟨ T₂ ⟩ handle h c₂ v 
--

--
-- TODO: define the first-order effect setup in terms of modular carriers
-- etc... to be able to make a more clear argument that we can borrow the
-- correctness proof from the paper?
--
-- perhaps even replicate a proof using postulated parametricity
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


  maybe-lemma : ∀ {f : A → Free ε B} {z y : Free ε B} {x : Maybe A} → (∀ x′ → x ≡ just x′ → f x′ ≈ y) → (x ≡ nothing → z ≈ y) →  maybe′ f z x ≈ y 
  maybe-lemma {x = just _}  j n = j _ refl
  maybe-lemma {x = nothing} j n = n refl


-- Equivalence following from equations of the theory, specialized to empty continuations
≈-eq′ : (eq : □ Equation ε) → eq ◃ T → {δ : TypeContext (□-extract eq .Δ′)} → {γ : □-extract eq .Γ′ δ} → □-extract eq .lhs δ γ ≈⟨ T ⟩ □-extract eq .rhs δ γ
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

-- monadic bind respects syntactic equivalence of effect trees 
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

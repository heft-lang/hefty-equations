{-# OPTIONS --without-K #-} 

open import Effect.Base
open import Effect.Handle
open import Effect.Syntax.Free

open import Effect.Relation.Ternary.FirstOrderSeparation
open import Effect.Relation.Binary.FirstOrderInclusion

open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Relation.Unary.All renaming (map to map-all ; lookup to lookup-all)
open import Data.List.Relation.Unary.All.Properties using (++⁺)

open import Data.Nat
open import Data.Vec hiding (map ; _++_)
open import Data.Maybe using (Maybe ; just ; nothing ; maybe′)

open import Relation.Unary hiding (_∈_ ; _⊆_ ; _⟨⊎⟩_)
open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open import Data.Empty

open import Core.Functor
open import Core.Ternary
open import Core.Functor.Monad

open import Core.Container
open import Core.Logic
open import Core.MonotonePredicate Effect _≲_ 
open import Core.Extensionality

open import Function
open import Function.Construct.Symmetry using (↔-sym)
open import Function.Construct.Composition using (_↔-∘_)
open import Level

module Effect.Theory.FirstOrder where

variable c c₁ c₂ c₃ : Free ε A

-- We define type contexts as a product by induction over the length rather than
-- a vector. This gives us some useful η-eqalities that save some pattern
-- matches when defining theories.
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
eq-resp-⇿ : ε₁ ⇿ ε₂ → Equation ε₁ → Equation ε₂
eq-resp-⇿ eq = hmap-eq (eq .equivalence _ .Inverse.to) 

-- We say that an algebra "respects" an equation if folding with that algebra
-- over both the left- and right-hand-side of the equation produces equal results
Respects : Algebraᶜ ε A → Equation ε → Set₁
Respects alg eq =
  ∀ {δ γ k}
  →   fold-free k alg (eq .lhs δ γ)
    ≡ fold-free k alg (eq .rhs δ γ) 

-- Witnesses that an equations respects (extensional) equivalence of inclusion
-- witnesses
--
-- Equations are defined as a Kripke function space, and this requirement states
-- that the function used to define an equation can only *use* the fact that its
-- lower bound is included in the index, but not make any assumptions about
-- *how* this inclusion is constructed. In practice, we only use the inclusions
-- for injecting smart constructors, so it makes sense that extensional
-- equivalence of the witness used to inject results in identical trees.
--
-- (TODO) remark on the relation w/ functor laws for monotone predicates, which
-- would also be suffictient, but extremely tedious to maintain for every
-- predicate used throughout the development.
record Respects-⇔≲ {P : Effect → Set₁} (x : □ P ε) : Set₁ where
  field
    respects-⇔≲ : ∀ (i₁ i₂ : ε ≲ ε′) → i₁ ⇔≲ i₂ →  □⟨ x ⟩ i₁ ≡ □⟨ x ⟩ i₂ 

open Respects-⇔≲

-- A theory of an effect `ε` is simply a collection of equations
--
-- 
record Theory (ε : Effect) : Set₁ where
  no-eta-equality
  constructor ∥_∥
  field
    equations : List $ Equation ε

open Theory public

record ExtensibleTheory (ε : Effect) : Set₁ where
  field
    theory : □ Theory ε
    lawful : Respects-⇔≲ theory   

open ExtensibleTheory public

instance ext-theory-monotone : Monotone ExtensibleTheory
theory (ext-theory-monotone .weaken i T) = necessary (λ i′ → □⟨ T .theory ⟩ ≲-trans i i′)
respects-⇔≲ (lawful (ext-theory-monotone .weaken i T)) i₁ i₂ x = T .lawful .respects-⇔≲ _ _ $ ⇔≲-trans-congᵣ i i₁ i₂ x

infix 2 _◃_
-- A predicate asserting that a given equation is part of a theory
_◃_ : Equation ε → Theory ε → Set₁
eq ◃ T = eq ∈ T .equations

-- Theory inclusion
_⊆_ : Theory ε → Theory ε → Set₁
T₁ ⊆ T₂ = ∀ {eq} → eq ◃ T₁ → eq ◃ T₂ 

-- Effect theories are monotone predicates over effects 
instance theory-monotone : Monotone Theory
theory-monotone .weaken i T =
  ∥ (map (weaken i) $ T .equations)
  --∣ weaken-all-lawful i (T .equations) (T .lawful)
  ∥

◃-weaken : {eq : Equation ε} → ∀ T → eq ◃ T → (i : ε ≲ ε′) → weaken i eq ◃ weaken i T
◃-weaken T px i with T .equations 
◃-weaken T (here refl) _ | _ ∷ _  = here refl
◃-weaken T (there px)  i | _ ∷ xs = there (◃-weaken ∥ xs  ∥ px i)


-- Heterogeneous theory inclusion
module _ where

  -- Use a record to help type inference 
  record _≪_ (T₁ : ExtensibleTheory ε₁) (T₂ : ExtensibleTheory ε₂) : Set₁ where
    field
      ⦃ inc ⦄ : ε₁ ≲ ε₂
      sub     : ∀ {ε′} {eq} → (i′ : ε₂ ≲ ε′) → eq ◃ □⟨ T₁ .theory ⟩ ≲-trans inc i′ → eq ◃ □⟨ T₂ .theory ⟩ i′

  open _≪_ public 

  -- The following two lemmas witness that heterogeneous theory inclusion
  -- is a preorder

  module _ {T : ExtensibleTheory ε} where
  
    ≪-refl : T ≪ T
    inc ≪-refl      = ≲-refl
    sub ≪-refl i′ x =
      subst (λ ○ → _ ◃ ○)
        (respects-⇔≲ (T .lawful) (≲-trans ≲-refl i′) i′ (⇔≲-identityˡ i′))
        x

  module _ {T₁ : ExtensibleTheory ε₁} {T₂ : ExtensibleTheory ε₂} {T₃ : ExtensibleTheory ε₃} where

    ≪-trans : T₁ ≪ T₂ → T₂ ≪ T₃ → T₁ ≪ T₃
    inc (≪-trans sub₁ sub₂)      = ≲-trans (sub₁ .inc) (sub₂ .inc)
    sub (≪-trans sub₁ sub₂) i′ x =
      sub₂ .sub i′
        ( sub₁ .sub (≲-trans (sub₂ .inc) i′)
          ( subst
            ( λ ○ → _ ◃ ○ )
            ( respects-⇔≲
                (T₁ .lawful)
                (≲-trans (≲-trans (inc sub₁) (inc sub₂)) i′)
                (≲-trans (inc sub₁) (≲-trans (sub₂ .inc) i′))
                (⇔≲-assoc (sub₁ .inc) (sub₂ .inc) i′)
            ) x ))
 
-- eq-lawful :
--   ∀ {ε}
--   → {ctx ret : {Effect} → TypeContext Δ → Set}
--   → {lhs rhs : {ε′ : Effect} → ⦃ ε ≲ ε′ ⦄ → Π[ ctx {ε′} ⇒ ret {ε′} ⊢ Free ε′ ]}
--   → ( ∀ {ε′}
--       → (i₁ i₂ : ε ≲ ε′) {δ : TypeContext Δ} {γ : ctx δ}
--       → i₁ ⇔≲ i₂ 
--       → lhs ⦃ i₁ ⦄ δ γ ≡ lhs ⦃ i₂ ⦄ δ γ
--     )
--   → ( ∀ {ε′}
--       → (i₁ i₂ : ε ≲ ε′) {δ : TypeContext Δ} {γ : ctx δ}
--       → i₁ ⇔≲ i₂ 
--       → rhs ⦃ i₁ ⦄ δ γ ≡ rhs ⦃ i₂ ⦄ δ γ
--     )
--     ------------------------------------------------------
--   → Respects-⇔≲ (necessary λ {ε} i → lhs ⦃ i ⦄ ≗ rhs ⦃ i ⦄)
-- respects-⇔≲ (eq-lawful l r) i₁ i₂ eqv =
--   cong₂ _≗_
--     (pfext _ _ λ δ → pfext _ _ λ γ → l i₁ i₂ eqv)
--     (pfext _ _ λ δ → pfext _ _ λ γ → r i₁ i₂ eqv)

open _⇔≲_ 

♯-resp-⇔≲ : {i₁ i₂ : ε₁ ≲ ε₂} → i₁ ⇔≲ i₂ → (m : Free ε₁ A) → ♯ ⦃ i₁ ⦄ m ≡ ♯ ⦃ i₂ ⦄ m
♯-resp-⇔≲ eqv (pure x)           = refl
♯-resp-⇔≲ {i₁ = i₁} {i₂} eqv (impure ⟨ c , k ⟩) =
  begin
    ♯ ⦃ i₁ ⦄ (impure ⟨ c , k ⟩)
  ≡⟨⟩ 
    hmap-free (inj ⦃ i₁ ⦄) (impure ⟨ c , k ⟩)
  ≡⟨ cong (λ ○ → hmap-free (λ {X} x → ○ X x) (impure ⟨ c , k ⟩)) (pfext _ _ λ X → pfext _ _ λ x → eqv .≗-inj {X} {x}) ⟩
    hmap-free (inj ⦃ i₂ ⦄) (impure ⟨ c , k ⟩) 
  ≡⟨⟩ 
    ♯ ⦃ i₂ ⦄ (impure ⟨ c , k ⟩)
  ∎
  where open ≡-Reasoning

>>=-resp-⇔≲ :
  ∀ {i₁ i₂ : ε₁ ≲ ε₂} → i₁ ⇔≲ i₂ 
  → (m : ε₁ ≲ ε₂ → Free ε₂ A)
  → (k : ε₁ ≲ ε₂ → A → Free ε₂ B)
  → m i₁ ≡ m i₂
  → (∀ x → k i₁ x ≡ k i₂ x)
    -----------------------------
  → m i₁ >>= k i₁ ≡ m i₂ >>= k i₂
>>=-resp-⇔≲ x m k px qx = cong₂ _>>=_ px (extensionality qx)


-- Coproduct of effect theories
_⟨+⟩_ : ∀[ Theory ⇒ Theory ⇒ Theory ]
(T₁ ⟨+⟩ T₂) .equations = T₁ .equations ++ T₂ .equations

-- Coproduct of extensible theories
_⟨⊎⟩_ : ∀[ ExtensibleTheory ⇒ ExtensibleTheory ⇒ ExtensibleTheory ]
theory (T₁ ⟨⊎⟩ T₂) = necessary λ i → (□⟨ T₁ .theory ⟩ i) ⟨+⟩ (□⟨ T₂ .theory ⟩ i)
respects-⇔≲ (lawful (T₁ ⟨⊎⟩ T₂)) i₁ i₂ x
  rewrite T₁ .lawful .respects-⇔≲ i₁ i₂ x
  | T₂ .lawful .respects-⇔≲ i₁ i₂ x = refl

-- Sum of effect theories
_[+]_ : Theory ε₁ → Theory ε₂ → Theory (ε₁ ⊕ᶜ ε₂) 
_[+]_ {ε₁} {ε₂} T₁ T₂ = weaken (≲-⊕ᶜ-left ε₂) T₁ ⟨+⟩ weaken (≲-⊕ᶜ-right ε₁) T₂

◃-⟨+⟩-left : ∀ {eq : Equation ε} → (T₁ T₂ : Theory ε) → eq ◃ T₁ → eq ◃ (T₁ ⟨+⟩ T₂)
◃-⟨+⟩-left T₁ T₂ px = ∈-++⁺ˡ px

◃-⟨+⟩-right : ∀ {eq : Equation ε} → (T₁ T₂ : Theory ε) → eq ◃ T₂ → eq ◃ (T₁ ⟨+⟩ T₂)
◃-⟨+⟩-right T₁ T₂ px = ∈-++⁺ʳ (T₁ .equations) px

-- "Heterogeneous" composition of effect theories" 
compose-theory : ∀[ (Theory ✴ Theory) ⇒ Theory ]
compose-theory (T₁ ✴⟨ σ ⟩ T₂) = weaken (≲-∙-left σ) T₁ ⟨+⟩ weaken (≲-∙-right σ) T₂

compose-ext-theory : ∀[ (ExtensibleTheory ✴ ExtensibleTheory) ⇒ ExtensibleTheory ]
compose-ext-theory (T₁ ✴⟨ σ ⟩ T₂) = weaken (≲-∙-left σ) T₁ ⟨⊎⟩ weaken (≲-∙-right σ) T₂

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

  ≈-eq    : (eq : Equation ε)
          → (px : eq ◃ T)  
          → (δ  : TypeContext (eq .Δ′))
          → (γ  : eq .Γ′ δ)
          → (k  : R′ eq δ → Free ε A) 
            -------------------------------------------
          → eq .lhs δ γ >>= k ≈⟨ T ⟩ eq .rhs δ γ >>= k
          
_≈[_]_ : ⦃ ε₁ ≲ ε₂ ⦄ → Free ε₂ A → ExtensibleTheory ε₁ → Free ε₂ A → Set₁
_≈[_]_ ⦃ i ⦄ m₁ T m₂ = m₁ ≈⟨ □⟨ T .theory ⟩ i ⟩ m₂

≈-weaken :
  ∀ {T : ExtensibleTheory ε₁} {T′ : ExtensibleTheory ε₂}
  → (i : T ≪ T′)
  → ⦃ i′ : ε₂ ≲ ε′ ⦄
  → (m₁ m₂ : Free ε′ A)
  → _≈[_]_ ⦃ ≲-trans (i .inc) i′ ⦄ m₁ T  m₂
    ---------------------------------------
  → m₁ ≈[ T′ ] m₂
≈-weaken i₁ m₁                   .m₁                  ≈-refl             = ≈-refl
≈-weaken i₁ m₁                   m₂                   (≈-sym eq)         = ≈-sym (≈-weaken i₁ m₂ m₁ eq)
≈-weaken i₁ m₁                   m₂                   (≈-trans eq₁ eq₂)  = ≈-trans (≈-weaken i₁ m₁ _ eq₁) (≈-weaken i₁ _ _ eq₂)
≈-weaken i₁ .(impure ⟨ s , p₁ ⟩) .(impure ⟨ s , p₂ ⟩) (≈-cong s p₁ p₂ k) = ≈-cong s p₁ p₂ (≈-weaken i₁ _ _ k)
≈-weaken i₁ .(eq .lhs δ γ >>= k) .(eq .rhs δ γ >>= k) (≈-eq eq px δ γ k) = ≈-eq eq (i₁ .sub _ px) δ γ k

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


open Handler

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
  → {eq : Equation _}
  → eq ◃ T
    --------------------------------------
  → Respects (h .hdl {A = A} {ε′ = ε′}) eq 

□-Correct : {P : Set} → ExtensibleTheory ε → Handler ε P F → Set₁
□-Correct T H = Correct (□⟨ T .theory ⟩ ≲-refl) H

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
≈-eq′ : (eq : Equation ε)
      → eq ◃ T → {δ : TypeContext (eq .Δ′)}
      → {γ : eq .Γ′ δ}
        -------------------------------
      → eq .lhs δ γ ≈⟨ T ⟩ eq .rhs δ γ
      
≈-eq′ eq px {δ} {γ} =
  begin
    eq .lhs δ γ
  ≈⟪ ≈-sym (>>=-idʳ-≈ _) ⟫
    eq .lhs δ γ >>= pure
  ≈⟪ ≈-eq eq px δ γ pure ⟫
    eq .rhs δ γ >>= pure 
  ≈⟪ >>=-idʳ-≈ _ ⟫
    eq .rhs δ γ
  ∎ 
  where open ≈-Reasoning _


-- monadic bind respects syntactic equivalence of effect trees in the left position 
>>=-resp-≈ˡ : {m₁ m₂ : Free ε A} (k : A → Free ε B) → m₁ ≈⟨ T ⟩ m₂ → m₁ >>= k ≈⟨ T ⟩ m₂ >>= k
>>=-resp-≈ˡ k ≈-refl                      = ≈-refl
>>=-resp-≈ˡ k (≈-sym eq)                  = ≈-sym (>>=-resp-≈ˡ k eq)
>>=-resp-≈ˡ k (≈-trans eq₁ eq₂)           = ≈-trans (>>=-resp-≈ˡ k eq₁) (>>=-resp-≈ˡ k eq₂)
>>=-resp-≈ˡ k (≈-cong s p₁ p₂ x)          = ≈-cong s ((_>>= k) ∘ p₁) ((_>>= k) ∘ p₂) λ {v} → >>=-resp-≈ˡ k (x {v})
>>=-resp-≈ˡ k (≈-eq eq px δ γ k′)         =
  begin
    (eq .lhs δ γ >>= k′) >>= k
  ≈⟪ >>=-assoc-≈ k′ k (eq .lhs δ γ) ⟫
    eq .lhs δ γ >>= (k′ >=> k)
  ≈⟪ ≈-eq eq px δ γ (k′ >=> k) ⟫
    eq .rhs δ γ >>= (k′ >=> k)
  ≈⟪ ≈-sym (>>=-assoc-≈ k′ k (eq .rhs δ γ)) ⟫
    (eq .rhs δ γ >>= k′) >>= k 
  ∎
  where open ≈-Reasoning _


-- monadic bind respects syntactic equivalence of effect trees in the right position 
>>=-resp-≈ʳ : {k₁ k₂ : A → Free ε B} (m : Free ε A) → (∀ a → k₁ a ≈⟨ T ⟩ k₂ a) → m >>= k₁ ≈⟨ T ⟩ m >>= k₂ 
>>=-resp-≈ʳ (pure x) eq = eq _
>>=-resp-≈ʳ {k₁ = k₁} {k₂} (impure ⟨ c , r ⟩) eq =
  begin
    impure ⟨ c , r ⟩ >>= k₁
  ≈⟪⟫ {- Definition of >>= -} 
    impure ⟨ c , (_>>= k₁) ∘ r ⟩  
  ≈⟪ ≈-cong c ((_>>= k₁) ∘ r) ((_>>= k₂) ∘ r) (>>=-resp-≈ʳ (r _) eq) ⟫
    impure ⟨ c , (_>>= k₂) ∘ r ⟩  
  ≈⟪⟫ {- Definition of >>= -}  
    impure ⟨ c , r ⟩ >>= k₂
  ∎
  where open ≈-Reasoning _ 

impure-injectiveˡ :
  ∀ {ε} {c₁ c₂ : ε .shape} {k₁ : ε .position c₁ → Free ε A} {k₂ : ε .position c₂ → Free ε A}
  → impure ⟨ c₁ , k₁ ⟩ ≡ impure ⟨ c₂ , k₂ ⟩ → c₁ ≡ c₂
impure-injectiveˡ refl = refl
 
impure-injectiveʳ :
  ∀ {ε} {c₁ c₂ : ε .shape} {k₁ : ε .position c₁ → Free ε A} {k₂ : ε .position c₂ → Free ε A}
  → (eq : impure ⟨ c₁ , k₁ ⟩ ≡ impure ⟨ c₂ , k₂ ⟩) → subst _ (impure-injectiveˡ eq) k₁ ≡ k₂
impure-injectiveʳ refl = refl


-- Heterogeneous theory inclusion respects heterogeneous composition in both positions
≪-compose-left :
  ∀ (T₁ : ExtensibleTheory ε₁) (T₂ : ExtensibleTheory ε₂)
  → (σ : ε₁ ∙ ε₂ ≈ ε)
     -----------------------------------------------
  → T₁ ≪ compose-ext-theory (T₁ ✴⟨ σ ⟩ T₂)
≪-compose-left T₁ T₂ σ .inc    = ≲-∙-left σ
≪-compose-left T₁ T₂ σ .sub px = ◃-⟨+⟩-left (□⟨ T₁ .theory ⟩ _) (□⟨ T₂ .theory ⟩ _) 


≪-compose-right :
  ∀ (T₁ : ExtensibleTheory ε₁) (T₂ : ExtensibleTheory ε₂)
  → (σ : ε₁ ∙ ε₂ ≈ ε)
    -------------------------------------------------
  → T₂ ≪ compose-ext-theory (T₁ ✴⟨ σ ⟩ T₂)
≪-compose-right T₁ T₂ σ .inc    = ≲-∙-right σ 
≪-compose-right T₁ T₂ σ .sub px = ◃-⟨+⟩-right (□⟨ T₁ .theory ⟩ _) (□⟨ T₂ .theory ⟩ _)


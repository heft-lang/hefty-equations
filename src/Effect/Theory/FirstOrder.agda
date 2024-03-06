{-# OPTIONS --without-K #-} 

open import Effect.Base
open import Effect.Separation
open import Effect.Inclusion 
open import Effect.Handle
open import Effect.Logic
open import Effect.Syntax.Free

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

open import Relation.Unary hiding (_∈_ ; _⊆_)
open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open import Data.Empty

open import Core.Functor
open import Core.Functor.Monad

open import Core.Container
open import Core.MonotonePredicate Effect _≲_ (≲-preorder .Preorder.isPreorder)
open import Core.Extensionality

open import Function
open import Function.Construct.Symmetry using (↔-sym)
open import Function.Construct.Composition using (_↔-∘_)
open import Level

module Effect.Theory.FirstOrder where

open Connectives

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
Respects : Algebraᶜ ε A → □ Equation ε → Set₁
Respects alg eq =
  ∀ {δ γ k}
  →   fold-free k alg (□-extract eq .lhs δ γ)
    ≡ fold-free k alg (□-extract eq .rhs δ γ) 

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
record Respects-⇔≲ (eq : □ Equation ε) : Set₁ where
  field
    respects-⇔≲ : ∀ (i₁ i₂ : ε ≲ ε′) → i₁ ⇔≲ i₂ →  □⟨ eq ⟩ i₁ ≡ □⟨ eq ⟩ i₂ 

open Respects-⇔≲

-- A theory of an effect `ε` is simply a collection of equations
--
-- 
record Theory (ε : Effect) : Set₁ where
  no-eta-equality
  constructor ∥_∣_∥
  field
    equations : List $ □ Equation ε
    lawful    : All Respects-⇔≲ equations

open Theory public

-- A predicate asserting that a given equation is part of a theory
_◃_ : □ Equation ε → Theory ε → Set₁
eq ◃ T = eq ∈ T .equations

-- Theory inclusion
_⊆_ : Theory ε → Theory ε → Set₁
T₁ ⊆ T₂ = ∀ {eq} → eq ◃ T₁ → eq ◃ T₂ 

weaken-lawful
  : (i : ε ≲ ε′)
  → (eq : □ Equation ε)
  → Respects-⇔≲ eq
  → Respects-⇔≲ (weaken i eq)
weaken-lawful i₁ eq x = record
  { respects-⇔≲ =
      λ i₂ i₃ eqv →
        x .respects-⇔≲
         (≲-trans i₁ i₂)
         (≲-trans i₁ i₃)
         (⇔≲-trans-congᵣ i₁ i₂ i₃ eqv)
  } 

weaken-all-lawful
  : (i : ε ≲ ε′)
  → (eqs : List (□ Equation ε))
  → All Respects-⇔≲ eqs
  → All Respects-⇔≲ (map (weaken i) eqs)
weaken-all-lawful i []         []         = []
weaken-all-lawful i (eq ∷ eqs) (lx ∷ lxs) =
  weaken-lawful i eq lx ∷ weaken-all-lawful i eqs lxs

-- Effect theories are monotone predicates over effects 
instance theory-monotone : Monotone Theory
theory-monotone .weaken i T =
  ∥ (map (weaken i) $ T .equations)
  ∣ weaken-all-lawful i (T .equations) (T .lawful)
  ∥

resp-lawful
  : (px : ε ⇿ ε₁)
  → (eq : □ Equation ε)
  → Respects-⇔≲ eq
  → Respects-⇔≲ (□-resp-⇿ px eq) 
respects-⇔≲ (resp-lawful ε⇿ε₁ eq x) i₂ i₃ eqv =
  x .respects-⇔≲
    (≲-respects-⇿ˡ (⇿-sym ε⇿ε₁) i₂)
    (≲-respects-⇿ˡ (⇿-sym ε⇿ε₁) i₃)
    (⇔≲-resp-⇿ˡ i₂ i₃ (⇿-sym ε⇿ε₁) eqv)

resp-all-lawful
  : (px : ε ⇿ ε₁)
  → (eqs : List (□ Equation ε))
  → All Respects-⇔≲ eqs
  → All Respects-⇔≲ (map (□-resp-⇿ px) eqs) 
resp-all-lawful px .[]      []         = []
resp-all-lawful px .(_ ∷ _) (lx ∷ lxs) = resp-lawful px _ lx ∷ resp-all-lawful px _ lxs

theory-resp-⇿ : ε₁ ⇿ ε₂ → Theory ε₁ → Theory ε₂ 
theory-resp-⇿ eqv T =
  ∥ map (□-resp-⇿ eqv) $ T .equations
  ∣ resp-all-lawful eqv (T .equations) (T .lawful)
  ∥

◃-weaken : {eq : □ Equation ε} → ∀ T → eq ◃ T → (i : ε ≲ ε′) → weaken i eq ◃ weaken i T
◃-weaken T px i with T .equations | T .lawful
◃-weaken T (here refl) _ | _ ∷ _  | _       = here refl
◃-weaken T (there px)  i | _ ∷ xs | _ ∷ pxs = there (◃-weaken ∥ xs ∣ pxs ∥ px i)


-- Heterogeneous theory inclusion
module _ where

  -- Use a record to help type inference 
  record _≪_ (T₁ : Theory ε₁) (T₂ : Theory ε₂) : Set₁ where
    field
      inc : ε₁ ≲ ε₂
      sub : ∀ {eq} → eq ◃ T₁ → weaken inc eq ◃ T₂ 

  open _≪_ public 

  -- The following two lemmas witness that heterogeneous theory inclusion
  -- is a preorder

  ≪-refl : {T : Theory ε} → T ≪ T
  inc ≪-refl = ≲-refl
  sub (≪-refl {T = T}) {eq} x =
    subst
      (_◃ T)
      ( cong
          (λ ○ → necessary λ {ε′} i → ○ ε′ i)
          ( pfext _ _ λ ε′ → pfext _ _ λ i →
              lookup-all (T .lawful) x .respects-⇔≲ i
                (≲-trans ≲-refl i)
                (⇔≲-sym _ _ (⇔≲-identityˡ i))
          )
      ) x

  ≪-trans :
    ∀ {T₁ : Theory ε₁} {T₂ : Theory ε₂} {T : Theory ε}
    → T₁ ≪ T₂ → T₂ ≪ T
      ----------------------------
    → T₁ ≪ T
  inc (≪-trans lq₁ lq₂) = ≲-trans (lq₁ .inc) (lq₂ .inc)
  sub (≪-trans {T₁ = T₁} {T = T} lq₁ lq₂) {eq} x =
    subst
      (_◃ T)
      ( cong
          (λ ○ → necessary λ {ε′} i → ○ ε′ i )
          (  pfext _ _ λ ε′ → pfext _ _ λ i →
               lookup-all
                 (T₁ .lawful)
                 x .respects-⇔≲
                   (≲-trans (inc lq₁) (≲-trans (inc lq₂) i))
                   (≲-trans (≲-trans (lq₁ .inc) (lq₂ .inc)) i)
                   (⇔≲-sym _ _ $ ⇔≲-assoc (lq₁ .inc) (lq₂ .inc) i)  ) )
      (lq₂ .sub (lq₁ .sub x))


 
eq-lawful :
  ∀ {ε}
  → {ctx ret : {Effect} → TypeContext Δ → Set}
  → {lhs rhs : {ε′ : Effect} → ⦃ ε ≲ ε′ ⦄ → Π[ ctx {ε′} ⇒ ret {ε′} ⊢ Free ε′ ]}
  → ( ∀ {ε′}
      → (i₁ i₂ : ε ≲ ε′) {δ : TypeContext Δ} {γ : ctx δ}
      → i₁ ⇔≲ i₂ 
      → lhs ⦃ i₁ ⦄ δ γ ≡ lhs ⦃ i₂ ⦄ δ γ
    )
  → ( ∀ {ε′}
      → (i₁ i₂ : ε ≲ ε′) {δ : TypeContext Δ} {γ : ctx δ}
      → i₁ ⇔≲ i₂ 
      → rhs ⦃ i₁ ⦄ δ γ ≡ rhs ⦃ i₂ ⦄ δ γ
    )
    ------------------------------------------------------
  → Respects-⇔≲ (necessary λ {ε} i → lhs ⦃ i ⦄ ≗ rhs ⦃ i ⦄)
respects-⇔≲ (eq-lawful l r) i₁ i₂ eqv =
  cong₂ _≗_
    (pfext _ _ λ δ → pfext _ _ λ γ → l i₁ i₂ eqv)
    (pfext _ _ λ δ → pfext _ _ λ γ → r i₁ i₂ eqv)

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
(T₁ ⟨+⟩ T₂) .lawful    = ++⁺ (T₁ .lawful) (T₂ .lawful)

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
≪-compose-left :
  ∀ (T₁ : Theory ε₁) (T₂ : Theory ε₂)
  → (σ : ε₁ ∙ ε₂ ≈ ε)
     -----------------------------------------------
  → T₁ ≪ compose-theory (T₁ ✴⟨ σ ⟩ T₂)
≪-compose-left T₁ T₂ σ .inc    = ≲-∙-left σ
≪-compose-left T₁ T₂ σ .sub px =
  ◃-⟨+⟩-left
    (weaken (≲-∙-left σ)  T₁)
    (weaken (≲-∙-right σ) T₂)
    (◃-weaken T₁ px (≲-∙-left σ)) 


≪-compose-right :
  ∀ (T₁ : Theory ε₁) (T₂ : Theory ε₂)
  → (σ : ε₁ ∙ ε₂ ≈ ε)
    -------------------------------------------------
  → T₂ ≪ compose-theory (T₁ ✴⟨ σ ⟩ T₂)
≪-compose-right T₁ T₂ σ .inc    = ≲-∙-right σ 
≪-compose-right T₁ T₂ σ .sub px =
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
  → {eq : □ Equation _}
  → eq ◃ T
    --------------------------------------
  → Respects (h .hdl {A = A} {ε′ = ε′}) eq 

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
>>=-resp-≈ˡ : {m₁ m₂ : Free ε A} (k : A → Free ε B) → m₁ ≈⟨ T ⟩ m₂ → m₁ >>= k ≈⟨ T ⟩ m₂ >>= k
>>=-resp-≈ˡ k ≈-refl                      = ≈-refl
>>=-resp-≈ˡ k (≈-sym eq)                  = ≈-sym (>>=-resp-≈ˡ k eq)
>>=-resp-≈ˡ k (≈-trans eq₁ eq₂)           = ≈-trans (>>=-resp-≈ˡ k eq₁) (>>=-resp-≈ˡ k eq₂)
>>=-resp-≈ˡ k (≈-cong s p₁ p₂ x)          = ≈-cong s ((_>>= k) ∘ p₁) ((_>>= k) ∘ p₂) λ {v} → >>=-resp-≈ˡ k (x {v})
>>=-resp-≈ˡ k (≈-eq eq px δ γ k′)         =
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

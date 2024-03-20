{-# OPTIONS --without-K #-} 

open import Relation.Unary

open import Core.Functor
open import Core.Functor.NaturalTransformation
open import Core.Functor.Monad

open import Core.Container
open import Core.Signature
open import Core.Extensionality

open import Effect.Base
open import Effect.Syntax.Free

open import Data.Empty 
open import Data.Product
open import Data.Sum

open import Effect.Separation
open import Effect.Inclusion

open import Function hiding (_⇔_)

open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_]) hiding (naturality)

module Effect.Handle where

open Inverse
open Union

{- Semantics for 1st order effects -}


-- Reordering of effect rows in an effect tree according to a given separation witness.
--
-- Reordering is a monad morphism between the respective free monads, so it
-- respects the monadic structure of Free
module _ where 

  reorder : ε₁ ∙ ε₂ ≈ ε′ → ∀[ Free ε′ ⇒ Free (ε₁ ⊕ᶜ ε₂) ]
  reorder σ = hmap-free (Union.proj σ)

  reorder⁻¹ : ε₁ ∙ ε₂ ≈ ε′ → ∀[ Free (ε₁ ⊕ᶜ ε₂) ⇒ Free ε′ ]
  reorder⁻¹ σ = hmap-free (Union.proj⁻¹ σ)

  reorder-inv : (σ : ε₁ ∙ ε₂ ≈ ε′) → (m : Free ε′ A) → reorder⁻¹ σ (reorder σ m) ≡ m
  reorder-inv {ε₁ = ε₁} {ε₂ = ε₂} {A = A} σ m =
    begin
      reorder⁻¹ σ (reorder σ m)
    ≡⟨⟩ 
      hmap-free (Union.proj⁻¹ σ) (hmap-free (Union.proj σ) m)
    ≡⟨ sym $ hmap-∘ {B = ⟦ ε₁ ⟧ᶜ A} {D = ⟦ ε₂ ⟧ᶜ A} m (Union.proj σ) (Union.proj⁻¹ σ) (proj-natural σ) ⟩ 
      hmap-free (Union.proj⁻¹ σ ∘ Union.proj σ ) m
    ≡⟨ cong (λ ○ → hmap-free (λ {A} → ○ A) m ) (pfext _ _ λ X → extensionality λ x → Union.union σ .equivalence X .inverse .proj₁ {x = x} refl) ⟩ 
      hmap-free id m
    ≡⟨ hmap-id m ⟩
      m
    ∎
    where open ≡-Reasoning

  reorder-coherent :
    ∀ (m : Free ε A) (k : A → Free ε B)
    → (σ : ε₁ ∙ ε₂ ≈ ε)
      ---------------------------------------------------
    → reorder σ (m >>= k) ≡ reorder σ m >>= reorder σ ∘ k
  reorder-coherent (pure x)           k σ = refl
  reorder-coherent {ε₁ = ε₁} {ε₂ = ε₂} (impure ⟨ c , r ⟩) k σ = 
    begin
      reorder σ (impure ⟨ c , r ⟩ >>= k)
    ≡⟨⟩ 
      impure (Union.proj σ ⟨ (c , reorder σ ∘ (r >=> k)) ⟩)
    ≡⟨ cong (λ ○ → impure (Union.proj σ ⟨ c , ○ ⟩)) (extensionality λ y → reorder-coherent (r y) k σ) ⟩ 
      impure (proj σ ⟨ c , ((reorder σ ∘ r) >=> (reorder σ ∘ k)) ⟩)
    ≡⟨ cong impure (proj-natural σ .commute {f = _>>= reorder σ ∘ k} ⟨ c , reorder σ ∘ r ⟩) ⟩ 
      impure (fmap {F = ⟦ ε₁ ⊕ᶜ ε₂ ⟧ᶜ} (_>>= reorder σ ∘ k) (Union.proj σ ⟨ c , reorder σ ∘ r ⟩)) 
    ≡⟨⟩
      impure (Union.proj σ ⟨ c , reorder σ ∘ r ⟩) >>= reorder σ ∘ k
    ≡⟨⟩ 
      reorder σ (impure ⟨ c , r ⟩) >>= reorder σ ∘ k
    ∎
    where open ≡-Reasoning

  reorder-natural : (σ : ε₁ ∙ ε₂ ≈ ε) → Natural (reorder σ)
  reorder-natural σ = hmap-natural (proj σ) (proj-natural σ) 

  reorder-mm : (σ : ε₁ ∙ ε₂ ≈ ε) → MonadMorphism (Free ε) (Free (ε₁ ⊕ᶜ ε₂))
  reorder-mm σ = record
    { Ψ         = reorder σ
    ; Ψ-natural = reorder-natural σ
    ; resp-unit = refl
    ; resp-join = λ k₁ k₂ → extensionality λ x → reorder-coherent (k₁ x) k₂ σ
    }

weaken-lemma : (σ : ε₁ ∙ ε₂ ≈ ε) → (m : Free ε₂ A) → reorder σ (♯ʳ′ σ m) ≡ ♯ʳ ε₁ m
weaken-lemma               σ (pure _)           = refl
weaken-lemma {ε₁} {ε₂} {ε} σ (impure ⟨ c , r ⟩) =
  begin
    reorder σ (♯ʳ′ σ (impure ⟨ c , r ⟩))
  ≡⟨⟩ 
    hmap-free (proj σ) (impure (injb σ ⟨ c , ♯ʳ′ σ ∘ r ⟩) )
  ≡⟨⟩ 
    impure (proj σ (fmap (reorder σ) (injb σ ⟨ c , ♯ʳ′ σ ∘ r ⟩))) 
  ≡⟨ cong (impure ∘ proj σ) (sym $ injb-natural σ .commute {f = fmap (reorder σ)} ⟨ c , ♯ʳ′ σ ∘ r ⟩)  ⟩
    impure (proj σ (injb σ (fmap (reorder σ) ⟨ c , ♯ʳ′ σ ∘ r ⟩))) 
  ≡⟨ cong impure (σ .union .equivalence _ .inverse .proj₂ refl) ⟩ 
    impure ⟨ inj₂ c , (reorder σ ∘ ♯ʳ′ σ) ∘ r ⟩ 
  ≡⟨ cong (λ ○ → impure ⟨ inj₂ c , ○ ⟩) (extensionality $ weaken-lemma σ ∘ r) ⟩
    impure ⟨ inj₂ c , ♯ʳ ε₁ ∘ r ⟩ 
  ≡⟨⟩ {- Definition of ♯ʳ -}  
    ♯ʳ ε₁ (impure ⟨ c , r ⟩)
  ∎
  where open ≡-Reasoning


-- Handers of an effect are algebras over its signatures
record Handler (ε : Effect) (P : Set) (F : Set → Set) : Set₁ where

  M : Effect → Set → Set
  M ε A = P → Free ε (F A) 
  
  field
    {{ F-functor }} : Functor F
    {{ M-monad   }} : ∀[ M ⊢ Monad ]

    hdl         : ∀ {ε′} → Algebraᶜ ε (M ε′ A) 

  instance M-functor : ∀[ M ⊢ Functor ]
  M-functor = is-functor 

  field
    M-apply :
      ∀ {X Y} {f : X → Y} {g : M ε′ X} {p : P}
        ---------------------------------------------------------
      → fmap {F = M _} f g p ≡ (fmap {F = Free _} (fmap f) ∘ g) p 

    hdl-commute :
      ∀ {X Y : Set} (f : X → Y) (x : ⟦ ε ⟧ᶜ (M ε′ X))
        -----------------------------------------------------------
      → hdl .αᶜ (fmap {F = ⟦ _ ⟧ᶜ} (fmap f) x) ≡ fmap f (hdl .αᶜ x) 


  fwd : Algebraᶜ ε′ (M ε′ A)
  fwd .αᶜ ⟨ c , k ⟩ = (λ p → impure ⟨ c , flip k p ⟩) 


  fwd-commute :
     ∀ {X Y : Set} (f : X → Y) (x : ⟦ ε′ ⟧ᶜ (M ε′ X))
      -----------------------------------------------------------
    → fwd .αᶜ (fmap {F = ⟦ _ ⟧ᶜ} (fmap f) x) ≡ fmap f (fwd .αᶜ x)
  fwd-commute f ⟨ c , k ⟩ = extensionality λ p →
    begin
      fwd .αᶜ (fmap {F = ⟦ _ ⟧ᶜ} (fmap f) ⟨ c , k ⟩) p
    ≡⟨⟩ 
      fwd .αᶜ ⟨ (c , fmap f ∘ k) ⟩ p
    ≡⟨⟩ 
      impure ⟨ c , (λ x → fmap f (k x) p) ⟩
    ≡⟨ cong (λ ○ → impure ⟨ c , ○ ⟩) (extensionality λ _ → M-apply) ⟩ 
      impure ⟨ c , (λ x → fmap {F = Free _} (fmap f) (k x p)) ⟩ 
    ≡⟨ sym M-apply ⟩
      fmap f (λ p′ → impure ⟨ c , (λ x → k x p′) ⟩) p
    ≡⟨⟩ 
      fmap f (fwd .αᶜ ⟨ c , k ⟩) p
    ∎ 
    where open ≡-Reasoning

  hdl-alg-commute :
    ∀ {X Y : Set} (f : X → Y) (x : ⟦ ε ⊕ᶜ ε′ ⟧ᶜ (M ε′ X))
      ---------------------------------------------------------------------------------
    → (hdl ⟨⊕⟩ᶜ fwd) .αᶜ (fmap {F = ⟦ _ ⟧ᶜ} (fmap f) x) ≡ fmap f ((hdl ⟨⊕⟩ᶜ fwd) .αᶜ x)
  hdl-alg-commute f ⟨ inj₁ c , k ⟩
    = hdl-commute f ⟨ c , k ⟩
  hdl-alg-commute f ⟨ inj₂ c , k ⟩
    = fwd-commute f ⟨ (c , k) ⟩

  handle′ : ∀[ Free (ε ⊕ᶜ ε₂) ⇒ const P ⇒ F ⊢ Free ε₂ ]
  handle′ m x = fold-free return (hdl ⟨⊕⟩ᶜ fwd) m x 

  handle : ε ∙ ε₂ ≈ ε′ → ∀[ Free ε′ ⇒ const P ⇒ F ⊢ Free ε₂ ] 
  handle σ m x = handle′ (reorder σ m) x

  ℋ⟦_⟧ : ⦃ ε ≲ ε′ ⦄ → ∀[ Free ε′ ⇒ const P ⇒ F ⊢ Free ε′ ]
  ℋ⟦_⟧ ⦃ i ⦄ m = ♯ ⦃ _ , union-comm (i .proj₂) ⦄ ∘ handle (i .proj₂) m

  ℋ⟪_⟫ : ⦃ ε ≲ ε′ ⦄ → (A → Free ε′ B) → (A → P → Free ε′ (F B)) 
  ℋ⟪ k ⟫ x = ℋ⟦ k x ⟧ 

  ⇑_ : ∀ {ε} → ∀[ Free ε ⇒ M ε ]
  (⇑ m) p = m >>= flip return p

  {- Below we define some properties of handlers, which are necessary for
  writing proofs about elaborations that handle effects in sub-computations. -} 


  ------------------
  --- Modularity ---
  ------------------

  Modular′ : Set₁
  Modular′ =
    ∀ {B ε₂} (m : Free ε₂ B)
      ------------------------
    → handle′ (♯ʳ ε m) ≡ ⇑ m 
  
  -- Defines "modular handlers", that asserts that a handler leaves alone nodes in
  -- the tree containing commands of other effects than the effect it handles. 
  Modular : Set₁
  Modular =
    ∀ {B ε₂ ε′} (m : Free ε₂ B)
    → (σ : ε ∙ ε₂ ≈ ε′)
      --------------------------------------
    → handle σ (♯ʳ′ σ m) ≡ ⇑ m


  -----------------
  --- Coherence ---
  -----------------

  Coherent′ : Set₁
  Coherent′ =
    ∀ {B C ε₂}
    → (m : Free (ε ⊕ᶜ ε₂) B) (k : B → Free (ε ⊕ᶜ ε₂) C)
      -----------------------------------------------------------
    → handle′ {ε₂ = ε₂} (m >>= k) ≡ (handle′ m) >>= (handle′ ∘ k)


  Coherent : Set₁
  Coherent =
    ∀ {B C ε₂ ε′}
    → (σ : ε ∙ ε₂ ≈ ε′)
    → (m : Free ε′ B) (k : B → Free ε′ C)
      -------------------------------------------------
    → handle σ (m >>= k) ≡ handle σ m >>= handle σ ∘ k

  reordering-preserves-modularity : Modular′ → Modular
  reordering-preserves-modularity mod m σ =
    begin
      handle′ (reorder σ (♯ʳ′ σ m))
    ≡⟨ cong (λ ○ → handle′ ○) (weaken-lemma σ m) ⟩
      handle′ (♯ʳ ε m) 
    ≡⟨ mod m ⟩ 
      ⇑ m
    ∎
    where open ≡-Reasoning 

  reordering-preserves-coherence : Coherent′ → Coherent
  reordering-preserves-coherence C σ m k = 
    begin
      handle σ (m >>= k)
    ≡⟨⟩ 
      handle′ (reorder σ (m >>= k))
    ≡⟨ cong handle′ (reorder-coherent m k σ) ⟩ 
      handle′ (reorder σ m >>= reorder σ ∘ k)
    ≡⟨ C (reorder σ m) (reorder σ ∘ k) ⟩ 
      handle σ m >>= handle σ ∘ k
    ∎
    where open ≡-Reasoning


  -- Proves the "stricter" notion of modularity for handlers, i.e., if the effect
  -- to be handled is already at the front
  handle-modular′ : Modular′
  handle-modular′     (pure x)           = refl
  handle-modular′     (impure ⟨ c , r ⟩) = extensionality λ p →
    begin
      handle′ (♯ʳ ε (impure ⟨ c , r ⟩)) p
    ≡⟨ cong (λ ○ → impure ⟨ c , ○ ⟩) (extensionality λ x → cong (_$ p) $ handle-modular′ (r x)) ⟩
      (⇑ impure ⟨ c , r ⟩) p
    ∎
    where open ≡-Reasoning

  -- All handlers are modular 
  handle-modular : Modular
  handle-modular = reordering-preserves-modularity handle-modular′


  -- Proves that handlers are natural transformations
  module _ where 

    instance foo : ∀ {ε} → Functor (M ε) 
    foo = M-monad .F-functor

    handle-natural : (σ : ε ∙ ε₂ ≈ ε) → Natural (handle σ)
    handle-natural {ε₂ = ε₂} σ .commute {X} {Y} {f = f} = handle-commute

      where
        open ≡-Reasoning
        handle-commute : ∀ m → handle σ (fmap f m) ≡ fmap f (handle σ m) 
        handle-commute m  =
          begin
            handle σ (fmap f m)
          ≡⟨⟩ 
            handle′ (reorder σ (fmap f m))
          ≡⟨ cong handle′ (reorder-natural σ .commute m) ⟩
            handle′ (fmap f (reorder σ m)) 
          ≡⟨ handle′-commute (reorder σ m) ⟩ 
            fmap f (handle′ (reorder σ m))
          ≡⟨⟩ 
            fmap f (handle σ m)
          ∎
          where
            
            handle′-commute : (m : Free (ε ⊕ᶜ ε₂) X) → handle′ {ε₂ = ε₂} (fmap f m)  ≡ fmap f (handle′ m) 
            handle′-commute (pure x)           =
              begin
                handle′ (fmap f (pure x))
              ≡⟨⟩
                handle′ (pure (f x))
              ≡⟨⟩ 
                return (f x)
              ≡⟨ return-natural .commute x ⟩
                fmap f (return x)
              ≡⟨⟩ 
                fmap f (handle′ (pure x))
              ∎
            handle′-commute (impure ⟨ c , k ⟩) =
              begin
                handle′ (fmap f (impure ⟨ c , k ⟩))
              ≡⟨⟩ 
                handle′ (impure ⟨ c , fmap f ∘ k ⟩)
              ≡⟨⟩
                (hdl ⟨⊕⟩ᶜ fwd) .αᶜ ⟨ c , handle′ ∘ fmap f ∘ k ⟩
              ≡⟨ cong (λ ○ → (hdl ⟨⊕⟩ᶜ fwd) .αᶜ ⟨ c , ○ ⟩ ) (extensionality (handle′-commute ∘ k)) ⟩ 
                (hdl ⟨⊕⟩ᶜ fwd) .αᶜ ⟨ c , fmap f ∘ handle′ ∘ k ⟩
              ≡⟨⟩ 
                 (hdl ⟨⊕⟩ᶜ fwd) .αᶜ  (fmap {F = ⟦ _ ⟧ᶜ} (fmap f) ⟨ c , handle′ ∘ k ⟩)
              ≡⟨ hdl-alg-commute f ⟨ c , handle′ ∘ k ⟩ ⟩
                fmap f ((hdl ⟨⊕⟩ᶜ fwd) .αᶜ ⟨ c , handle′ ∘ k ⟩) 
              ≡⟨⟩ 
               fmap f (handle′ (impure ⟨ c , k ⟩))
              ∎

-- -- Show that handlers are monad morphisms
-- handle-mm :
--   ∀ ⦃ _ : Functor F ⦄
--   → (H : Handler ε A F)
--   → Coherent H
--   → ⦃ i : ε ≲ ε′ ⦄
--     ----------------------------------------
--   → MonadMorphism (Free ε′) (M H (i .proj₁))
-- handle-mm H C ⦃ i ⦄ = record
--   { Ψ         = handle H (i .proj₂)
--   ; Ψ-natural = handle-natural (i .proj₂) H 
--   ; resp-unit = extensionality resp-unit′
--   ; resp-join = λ f g → extensionality λ x → C (i .proj₂) (f x) g
--   }
--   where
--     open ≡-Reasoning
--     resp-unit′ : ∀ {B : Set} (x : B) → handle H (i .proj₂) (pure x) ≡ return x
--     resp-unit′ x =
--       begin
--         handle H (i .proj₂) (pure x)
--       ≡⟨⟩ 
--         handle′ H (reorder (i .proj₂) (pure x))
--       ≡⟨⟩ 
--         handle′ H (pure x)
--       ≡⟨⟩ 
--         fold-free return (H .hdl ⟨⊕⟩ᶜ fwd) (pure x)
--       ≡⟨⟩
--         return x
--       ∎


-- -- ℋ-mm :
-- --   ∀ (H : Handler ε A F)
-- --   → (C : Coherent H) 
-- --   → ⦃ ε ≲ ε′ ⦄ 
-- --     -----------------------------------------------
-- --   → MonadMorphism (Free ε′) (const A ⇒ F ⊢ Free ε′)
-- -- ℋ-mm H C ⦃ i ⦄ = ∘-mm (handle-mm H C) {!!}

-- -- ℋ-coherent :
-- --   ∀ {P : Set}
-- --   → ⦃ _ : ε ≲ ε′ ⦄
-- --   → ⦃ _ : ∀ {ε} → Monad (const P ⇒ F ⊢ Free ε) ⦄
-- --   → (H : Handler ε P F)
-- --   → let module Hd = Handler H in 
-- --     Coherent H
-- --   → (m : Free ε′ A) (k : A → Free ε′ B)
-- --     ---------------------------------------------------
-- --   → Hd.ℋ⟦ m >>= k ⟧ ≡ Hd.ℋ⟦ m ⟧ >>= λ x → Hd.ℋ⟦ k x ⟧
-- -- ℋ-coherent {ε = ε} {ε′ = ε′} ⦃ i ⦄ H C m k = 
-- --   begin
-- --     ℋ⟦ (m >>= k) ⟧′
-- --   ≡⟨⟩ 
-- --     ♯ ∘ (handle H (i .proj₂) (m >>= k))
-- --   ≡⟨ cong (♯ ∘_) (C (i .proj₂) m k) ⟩
-- --     ♯ ∘ (handle H (i .proj₂) m >>= λ x p → handle H (i .proj₂) (k x) p)
-- --   ≡⟨ {!!} ⟩ 
-- --     ♯ ∘ handle H (i .proj₂) m >>= (λ x p → ♯ (handle H (i .proj₂) (k x) p))
-- --   ≡⟨⟩ 
-- --     (ℋ⟦ m ⟧′ >>= ℋ⟦_⟧′ ∘ k)
-- --   ∎
-- --   where
-- --     ℋ⟦_⟧′ = ℋ⟦ H ⟧
-- --     instance inst : i .proj₁ ≲ ε′
-- --     inst = ε , union-comm (i .proj₂)

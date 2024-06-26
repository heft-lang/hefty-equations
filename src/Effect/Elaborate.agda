{-# OPTIONS --without-K #-} 

open import Relation.Unary

open import Core.Functor
open import Core.Functor.NaturalTransformation
open import Core.Functor.Monad

open import Core.Ternary
open import Core.Container
open import Core.Signature
open import Core.Extensionality
open import Core.Logic

open import Effect.Syntax.Free
open import Effect.Syntax.Hefty
open import Effect.Base

open import Data.Empty 
open import Data.Product
open import Data.Sum

open import Effect.Relation.Ternary.FirstOrderSeparation
open import Effect.Relation.Binary.FirstOrderInclusion
open import Effect.Relation.Ternary.HigherOrderSeparation
open import Effect.Relation.Binary.HigherOrderInclusion

open import Effect.Theory.FirstOrder

open import Function hiding (_⇔_)

open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality

open import Effect.Handle

module Effect.Elaborate where

open import Core.MonotonePredicate Effect _≲_ 

{- Semantics for higher-order effects -}

S : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (A → B → C) → (A → B) → A → C
S = λ x y z → x z (y z) 
  
record Elaboration (η : Effectᴴ) (ε : Effect) : Set₁ where
  field
    elab : □ (S (Algebra ∘ η) Free)  ε
    

  elaborate : ∀[ Hefty (η ε) ⇒ Free ε ]
  elaborate = fold-hefty pure (□⟨ elab ⟩ ≲-refl)   

  elaborate′ : ⦃ ε ≲ ε′ ⦄ → ∀[ Hefty (η ε′) ⇒ Free ε′ ]
  elaborate′ ⦃ i ⦄ = fold-hefty pure (□⟨ elab ⟩ i)

  ℰ⟦_⟧ = elaborate′

  -- Map `Hefty` continuations to `Free` continuations.
  --
  -- This witnesses that (the fold of) an elaboration algebra characterized by
  -- signatures `η` and `ε` defines a functor between the Kleisli categories of
  -- respectively the monads `Hefty (η ε)` and `Free ε`.
  ℰ⟪_⟫ : ⦃ ε ≲ ε′ ⦄ → (A → Hefty (η ε′) B) → (A → Free ε′ B)
  ℰ⟪ f ⟫ = λ x → ℰ⟦ f x ⟧   
   
  field
    -- Establishes that elaboration algebras commute with fmap in a suitable
    -- way. This allows us to show that elaborations are natural
    -- transformations.
    commutes :
      ∀ {A B : Set} {f : A → B}
      → (x : ⟦ η ε′ ⟧ (Free ε′) A)
        --------------------------------------------------------------------------
      → ⦃ i : ε ≲ ε′ ⦄ → (□⟨ elab ⟩ i) .α (fmap f x) ≡ fmap f ((□⟨ elab ⟩ i) .α x) 

    -- Coherence property for elaboration algebras, establishing that
    -- elaboration algebras distribute over Kleisli composition in a suitable
    -- way. From this notion of coherence we can derive that elaborations are
    -- monad morhpisms between Hefty trees and the free monad.
    coherent :
      ∀ {A B ε′ c s} → ⦃ i : ε ≲ ε′ ⦄
      → (k₁ : response (η _) c → Free ε′ A)
      → (k₂ : A → Free ε′ B)
        -------------------------------------------------------------------------------
      → (□⟨ elab ⟩ i) .α ⟪ c , k₁ >=> k₂ , s ⟫ ≡ (□⟨ elab ⟩ i) .α ⟪ c , k₁ , s ⟫ >>= k₂

  elab-natural : ∀ {ε′} → ⦃ _ : ε ≲ ε′ ⦄ → Natural ℰ⟦_⟧ 
  elab-natural ⦃ i ⦄ .commute = commute-elab
    where
      open ≡-Reasoning

      commute-elab :  ∀ {X Y} {f : X → Y} → (x : Hefty (η _) X) → ℰ⟦ (fmap f x) ⟧ ≡  fmap f ℰ⟦ x ⟧ 
      commute-elab (pure x) = refl
      commute-elab {f = f} (impure ⟪ c , k , s ⟫) =
        begin
          ℰ⟦ fmap f (impure ⟪ c , k , s ⟫) ⟧
        ≡⟨⟩
          ℰ⟦ impure ⟪ c , fmap f ∘ k  , s ⟫ ⟧
        ≡⟨⟩
          (□⟨ elab ⟩ i) .α ⟪ c , ℰ⟪ fmap f ∘ k ⟫ , ℰ⟦_⟧ ∘ s ⟫
        ≡⟨ cong (λ ○ → (□⟨ elab ⟩ i) .α ⟪ c , ○ , ℰ⟦_⟧ ∘ s ⟫) (extensionality λ x → commute-elab (k x)) ⟩
          (□⟨ elab ⟩ i) .α ⟪ c , fmap f ∘ ℰ⟪ k ⟫ , ℰ⟦_⟧ ∘ s ⟫ 
        ≡⟨⟩
          (□⟨ elab ⟩ i) .α (fmap f ⟪ c , ℰ⟪ k ⟫ , ℰ⟦_⟧ ∘ s ⟫)
        ≡⟨ commutes ⟪ c , ℰ⟪ k ⟫ , ℰ⟦_⟧ ∘ s ⟫ ⟩ 
          fmap f ((□⟨ elab ⟩ i) .α ⟪ c , ℰ⟪ k ⟫ , ℰ⟦_⟧ ∘ s ⟫) 
        ≡⟨⟩
          fmap f ℰ⟦ impure ⟪ c , k , s ⟫ ⟧
        ∎
  
  -- Elaborations respect identities
  elab-id : ⦃ _ : ε ≲ ε′ ⦄ → ℰ⟪ return {A = A} ⟫ ≡ return {F = Free ε′}
  elab-id = refl

  -- Show that pointwise elaborations respect Kleisli composition 
  mutual
    elab-∘′ : ∀ {B C : Set}
              → ⦃ _ : ε ≲ ε′ ⦄
              → (m :  Hefty (η ε′) B)
              → (k : B → Hefty (η ε′) C)
                ------------------------------------
              → ℰ⟦ m >>= k ⟧ ≡ ℰ⟦ m ⟧ >>= ℰ⟪ k ⟫
    elab-∘′ (pure x) k = refl
    elab-∘′ ⦃ i ⦄ (impure ⟪ c , k′ , s ⟫) k =
      begin
        ℰ⟦ impure ⟪ c , k′ , s ⟫ >>= k ⟧
      ≡⟨⟩ 
        ℰ⟦ impure ⟪ c , (k′ >=> k) , (_>>= pure) ∘ s ⟫ ⟧
      ≡⟨ cong (λ ○ → ℰ⟦ impure ⟪ c , (k′ >=> k) , ○ ⟫ ⟧) (extensionality $ λ ψ → >>=-idʳ (s ψ)) ⟩
        ℰ⟦ impure ⟪ c , (k′ >=> k) , s ⟫ ⟧
      ≡⟨⟩ 
        fold-hefty pure (□⟨ elab ⟩ i) (impure ⟪ c , (k′ >=> k) , s ⟫)
      ≡⟨⟩
        (□⟨ elab ⟩ i) .α ⟪ c , ℰ⟪ k′ >=> k ⟫ , ℰ⟦_⟧ ∘ s  ⟫ 
      ≡⟨ cong (λ ○ → (□⟨ elab ⟩ i) .α ⟪ c , ○ , ℰ⟦_⟧ ∘ s ⟫) (elab-∘ k′ k) ⟩
        (□⟨ elab ⟩ i) .α ⟪ c , (ℰ⟪ k′ ⟫ >=> ℰ⟪ k ⟫) , ℰ⟦_⟧ ∘ s ⟫ 
      ≡⟨ coherent ℰ⟪ k′ ⟫ ℰ⟪ k ⟫ ⟩ 
        (□⟨ elab ⟩ i) .α ⟪ c , ℰ⟪ k′ ⟫ , ℰ⟦_⟧ ∘ s ⟫ >>= ℰ⟪ k ⟫ 
      ≡⟨⟩ 
        fold-hefty pure (□⟨ elab ⟩ i) (impure ⟪ c , k′ , s ⟫) >>= ℰ⟪ k ⟫ 
      ≡⟨⟩ 
        ℰ⟦ impure ⟪ c , k′ , s ⟫ ⟧ >>= ℰ⟪ k ⟫
      ∎
      where
        open ≡-Reasoning

    -- Elaboration 
    elab-∘ : ∀ {A B C : Set}
             → ⦃ _ : ε ≲ ε′ ⦄
             → (k₁ : A → Hefty (η ε′) B)
             → (k₂ : B → Hefty (η ε′) C)
               ------------------------------------
             → ℰ⟪ k₁ >=> k₂ ⟫ ≡ ℰ⟪ k₁ ⟫ >=> ℰ⟪ k₂ ⟫
    elab-∘ ⦃ i ⦄ k₁ k₂ = extensionality λ x → elab-∘′ (k₁ x) k₂     

    -- Elaborations are a monad morphism between Hefty trees and the Free monad
    elab-mm : ∀ {ε′} → ⦃ _ : ε ≲ ε′ ⦄ → MonadMorphism (Hefty (η ε′)) (Free ε′)
    elab-mm = record
      { Ψ         = elaborate′
      ; Ψ-natural = elab-natural
      ; resp-unit = elab-id
      ; resp-join = elab-∘
      }

open Elaboration

--Sub-elaborations
record _⊑_ (e₁ : Elaboration η₁ ε₁) (e₂ : Elaboration η₂ ε₂) : Set₁ where
  field
    ⦃ ≲-eff  ⦄        : ε₁ ≲ ε₂
    ⦃ ≲-effᴴ ⦄        : η₁ ≲ η₂
    preserves-cases :
      ∀ {M}
      → (m : ⟦ η₁ ε₂ ⟧ M A)
      → (e′ : ∀[ M ⇒ Free ε₂ ])
        ---------------------------------------------
      →   (□⟨ e₁ .elab ⟩ ≲-eff ) .α (sig-hmap e′ m)
        ≡ (□⟨ e₂ .elab ⟩ ≲-refl) .α (sig-hmap e′ (injᴴ m))

open _⊑_ public 


⊑-refl : {e : Elaboration η ε} → e ⊑ e
≲-eff           ⊑-refl         = ≲-refl 
≲-effᴴ          ⊑-refl         = ≲ᴴ-refl
preserves-cases ⊑-refl m e′    = refl

module _ {e₁ : Elaboration η₁ ε₁} {e₂ : Elaboration η₂ ε₂} where 

  use-elab-def : 
    ∀  ⦃ ζ : e₁ ⊑ e₂ ⦄
    → (m : ⟦ η₁ ε₂ ⟧ (Hefty (η₂ ε₂)) A)
      ---------------------------------------------------
    →   elaborate e₂ (impure (injᴴ m))
      ≡ (□⟨ e₁ .elab ⟩ ζ .≲-eff) .α (sig-hmap (elaborate e₂) m)
  use-elab-def ⦃ ζ ⦄ m =
    begin
      elaborate e₂ (impure (injᴴ m))
    ≡⟨ (sym $ ζ .preserves-cases m (elaborate e₂)) ⟩
      (□⟨ e₁ .elab ⟩ ζ .≲-eff) .α (sig-hmap (elaborate e₂) m)
    ∎
    where
      open ≡-Reasoning

open □
open _✴_

instance elab-monotone : Monotone (Elaboration η)
elab-monotone .weaken i e .elab             = necessary (λ i′ → □⟨ e .elab ⟩ ≲-trans i i′)
elab-monotone .weaken i e .commutes x ⦃ i′ ⦄ = e .commutes x ⦃ ≲-trans i i′ ⦄ 
elab-monotone .weaken i e .coherent   ⦃ i′ ⦄ = λ k₁ k₂ → e .coherent ⦃ ≲-trans i i′ ⦄ k₁ k₂ 

-- "Homogeneous" composition of elaborations. Combines two elaborations that
-- assume the *same* lower bound on the effects that they elaborate into
_⟪⊕⟫_ : ∀[ Elaboration η₁ ⇒ Elaboration η₂ ⇒ Elaboration (η₁ ·⊕ η₂) ]
(e₁ ⟪⊕⟫ e₂) .elab                        = necessary λ i → (□⟨ e₁ .elab ⟩ i) ⟨⊕⟩ (□⟨ e₂ .elab ⟩ i)
(e₁ ⟪⊕⟫ e₂) .commutes ⟪ inj₁ c , k , s ⟫ = e₁ .commutes ⟪ c , k , s ⟫
(e₁ ⟪⊕⟫ e₂) .commutes ⟪ inj₂ c , k , s ⟫ = e₂ .commutes ⟪ c , k , s ⟫
(e₁ ⟪⊕⟫ e₂) .coherent {c = inj₁ x}       = e₁ .coherent
(e₁ ⟪⊕⟫ e₂) .coherent {c = inj₂ y}       = e₂ .coherent

⊑-⟪⊕⟫-left : ∀ {e₁ : Elaboration η₁ ε} → {e₂ : Elaboration η₂ ε} → e₁ ⊑ (e₁ ⟪⊕⟫ e₂)
≲-eff           ⊑-⟪⊕⟫-left        = ≲-refl  
≲-effᴴ          ⊑-⟪⊕⟫-left        = ·⊑-⊕-left
preserves-cases ⊑-⟪⊕⟫-left _ _  = refl 

⊑-⟪⊕⟫-right : ∀ {e₁ : Elaboration η₁ ε} → {e₂ : Elaboration η₂ ε} → e₂ ⊑ (e₁ ⟪⊕⟫ e₂)
≲-eff           ⊑-⟪⊕⟫-right        = ≲-refl  
≲-effᴴ          ⊑-⟪⊕⟫-right        = ·⊑-⊕-right
preserves-cases ⊑-⟪⊕⟫-right _ _      = refl

-- "Heterogeneous" composition of elaborations. Combines two elaborations that
-- assume a *different* lower bound on the algebraic effects that they elaborate
-- into
compose-elab : ∀[ (Elaboration η₁ ✴ Elaboration η₂) ⇒ Elaboration (η₁ ·⊕ η₂)  ]
compose-elab (e₁ ✴⟨ σ ⟩ e₂) = weaken (≲-∙-left σ) e₁ ⟪⊕⟫ weaken (≲-∙-right σ) e₂

-- -- The adjoint relation between separating conjuntion and implication gives us
-- -- an equivalent operation that, given an elaboration, returns an "extension
-- -- operation" that captures the concept of extending other elaborations with a
-- -- known/given elaboration. The separating implication operation deals with the
-- -- different lower bounds these elaborations assume on the algebraic effects
-- -- they elaborate into.
-- --
-- -- Or, in other words, we can curry (and thus partially apply) the heterogeneous
-- -- composition operation.
-- extend-with : ∀[ Elaboration η₁ ⇒ (Elaboration η₂ ─✴ Elaboration (η₁ ·⊕ η₂)) ]
-- extend-with = ✴-curry compose-elab

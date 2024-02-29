{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Functor.Monad
open import Core.Functor.NaturalTransformation

open import Core.Container
open import Core.Extensionality

open import Effect.Base
open import Effect.Handle
open import Effect.Separation
open import Effect.Inclusion
open import Effect.Logic
open import Effect.Syntax.Free

open import Data.Unit
open import Data.Maybe hiding (_>>=_)
open import Data.Product
open import Data.Vec
open import Data.Sum
open import Data.Empty

open import Function 

open import Effect.Theory.FirstOrder

open import Effect.Instance.Abort.Syntax
open import Effect.Instance.Abort.Theory

open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open import Relation.Unary

open import Level

open import Core.MonotonePredicate Effect _≲_

module Effect.Instance.Abort.Handler where

open Connectives hiding (_⟨_⟩_)

instance maybe-functor : Functor {a = 0ℓ} Maybe
maybe-functor = record
  { fmap    = λ f → maybe (just ∘ f) nothing
  ; fmap-id = extensionality (maybe (λ _ → refl) refl)
  ; fmap-∘  = λ f g → extensionality (maybe (λ _ → refl) refl)
  } 

⊤-functor : Functor F → Functor (const ⊤ ⇒ F)
⊤-functor ff = record
  { fmap    = λ where f x tt → fmap ⦃ ff ⦄ f (x tt)
  ; fmap-id = pfext _ _
      λ m → cong (λ where ○ tt → ○ (m tt)) $ fmap-id ⦃ ff ⦄ 
  ; fmap-∘  = λ f g → pfext _ _
      λ m → cong (λ where ○ tt → ○ (m tt)) (fmap-∘ ⦃ ff ⦄ f g)
  } 

instance abortT-functor : Functor (const ⊤ ⇒ Maybe ⊢ Free ε)
abortT-functor = ⊤-functor (∘-functor maybe-functor free-functor) 

open ≡-Reasoning

instance readerT-monad : Monad (const ⊤ ⇒ Maybe ⊢ Free ε)
readerT-monad = record
  { return         = λ where x tt → pure (just x)
  ; _∗             = λ where f m tt → m tt >>= maybe′ (flip f tt) (pure nothing)
  ; >>=-idˡ        = λ x k → refl
  ; >>=-idʳ        = λ m → extensionality λ where
      tt → begin
             m tt >>= maybe′ (pure ∘ just) (pure nothing)
           ≡⟨ cong (m tt >>=_) (extensionality (maybe (λ _ → refl) refl)) ⟩ 
             m tt >>= pure 
           ≡⟨ >>=-idʳ (m tt) ⟩
             m tt
           ∎ 
  ; >>=-assoc      = λ k₁ k₂ m → extensionality λ where
      tt → begin
             (m tt >>= maybe′ (flip k₁ tt) (pure nothing)) >>= maybe′ (flip k₂ tt) (pure nothing)
           ≡⟨ >>=-assoc _ _ (m tt) ⟩
             m tt >>= (maybe′ (flip k₁ tt) (pure nothing) >=> maybe′ (flip k₂ tt) (pure nothing)) 
           ≡⟨ cong (m tt >>=_) (extensionality (maybe (λ _ → refl) refl)) ⟩ 
             m tt >>= maybe′ (λ x → k₁ x tt >>= maybe′ (flip k₂ tt) (pure nothing)) (pure nothing)
           ∎
  ; return-natural = λ where .commute x → refl
  } 

AbortHandler : Handler Abort ⊤ Maybe
Handler.F-functor   AbortHandler = maybe-functor
Handler.M-monad     AbortHandler = readerT-monad

Handler.hdl AbortHandler .αᶜ ⟨ `abort , k ⟩ = λ where tt → pure nothing

Handler.M-apply     AbortHandler                  = refl
Handler.hdl-commute AbortHandler f ⟨ `abort , k ⟩ = refl


open Handler

handleAbort : Abort ∙ ε ≈ ε′ → Free ε′ A → Free ε (Maybe A)
handleAbort σ m = handle AbortHandler σ m tt


module Properties where

  modular : Modular AbortHandler
  modular = handle-modular AbortHandler 
 
  correct : Correct AbortTheory AbortHandler 
  correct (here refl) = refl

  handle-abort-is-nothing : (σ : Abort ∙ ε ≈ ε′) → handleAbort {A = A} σ (abort ⦃ _ , σ ⦄) ≡ pure nothing
  handle-abort-is-nothing {ε} σ =
    begin
      handleAbort σ abort
    ≡⟨⟩ 
      handle AbortHandler σ abort tt
    ≡⟨⟩
      handle AbortHandler σ (♯ (impure ⟨ `abort , ⊥-elim ⟩)) tt
    ≡⟨⟩ 
      handle′ AbortHandler (reorder σ (impure (inj ⟨ `abort , (λ x → fold-free pure inject (⊥-elim x)) ⟩))) tt
    ≡⟨⟩
      handle′ AbortHandler (fold-free pure (λ where .αᶜ → impure ∘ proj σ) $ impure (inj ⟨ `abort , (λ x → fold-free pure inject (⊥-elim x)) ⟩)) tt
    ≡⟨⟩ 
      handle′ AbortHandler (impure (proj σ (fmap (reorder σ) (inj ⟨ `abort , ((λ x → fold-free pure inject (⊥-elim x))) ⟩)))) tt
    ≡⟨ cong (flip (handle′ AbortHandler) tt ∘ impure ∘ proj σ)
       ( sym (inj-natural .commute {f = reorder σ} _)
       ) ⟩
      flip (handle′ AbortHandler) tt (impure (proj σ (inj (⟨ (`abort , (λ x → reorder σ $ fold-free pure inject (⊥-elim x))) ⟩)))) 
    ≡⟨ cong (flip (handle′ AbortHandler) tt ∘ impure)
         ( σ .union .equivalence _ .inverse .proj₂
           ( injˡ {C₁ = Abort} ε ⟨ (`abort , (λ x → reorder σ $ fold-free pure inject (⊥-elim x))) ⟩)
         ) ⟩
      flip (handle′ AbortHandler) tt (impure (injˡ {C₁ = Abort} ε ⟨ (`abort , (λ x → reorder σ $ fold-free pure inject (⊥-elim x))) ⟩)) 
    ≡⟨⟩ 
      pure nothing
    ∎
    where
      open Union
      open Inverse 
      open ≡-Reasoning
      instance inst : Abort ≲ _
      inst = _ , σ
  

open import Core.Functor
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


open import Core.MonotonePredicate Effect _≲_

module Effect.Instance.Abort.Handler where

open Connectives hiding (_⟨_⟩_)

AbortHandler : Handler Abort ⊤ Maybe
AbortHandler = record
  { gen = λ x _ → just x
  ; hdl = record
    { αᶜ = λ where ⟨ `abort , _ ⟩ tt → return nothing
    }
  } 

handleAbort : Abort ∙ ε ≈ ε′ → Free ε′ A → Free ε (Maybe A)
handleAbort σ = handle AbortHandler σ tt


module Properties where

  modular : Modular AbortHandler
  modular = handle-modular AbortHandler 

  -- TODO: there's really only one relevant case here. Can we factor the proof
  -- such that we only have to provide that case?
  adequate′ : Adequate′ AbortHandler AbortTheory 
  adequate′ tt (pure x)                      (pure .x)                     _ refl = ≈-refl
  adequate′ tt (pure _)                      (impure ⟨ inj₁ `abort , _  ⟩) _ ()
  adequate′ tt (impure ⟨ inj₁ `abort , _  ⟩) (pure _)                      _ ()
  adequate′ {B} {ε₂  = ε₂} tt (impure ⟨ inj₁ `abort , k₁ ⟩) (impure ⟨ inj₁ `abort , k₂ ⟩) {T′} i eq =
    begin
      impure ⟨ inj₁ `abort , k₁ ⟩
    ≈⟪ ≡-to-≈ (cong (λ ○ → impure ⟨ inj₁ `abort , ○ ⟩) (extensionality λ())) ⟫
      abort >>= k₁ 
    ≈⟪ ≈-eq′ (weaken inst bind-abort) (i (here refl)) ⟫ 
      abort   
    ≈⟪ ≈-sym (≈-eq′ (weaken inst bind-abort) (i (here refl))) ⟫
      abort >>= k₂ 
    ≈⟪ ≈-sym (≡-to-≈ (cong (λ ○ → impure ⟨ inj₁ `abort , ○ ⟩) (extensionality λ()))) ⟫ 
      impure ⟨ inj₁ `abort , k₂ ⟩
    ∎
    where
      open ≈-Reasoning T′
      instance inst : Abort ≲ (Abort ⊕ᶜ ε₂)
      inst = ≲-⊕ᶜ-left ε₂ 
  adequate′ tt (impure ⟨ inj₁ `abort , _  ⟩) (impure ⟨ inj₂ _      , _  ⟩) _ ()
  adequate′ tt (impure ⟨ inj₂ _      , _  ⟩) (impure ⟨ inj₁ `abort , _  ⟩) _ ()
  adequate′ tt (impure ⟨ inj₂ c₁     , k₁ ⟩) (impure ⟨ inj₂ c₂     , k₂ ⟩) i eq
    with impure-injectiveˡ eq
  ... | refl = ≈-cong (inj₂ c₁) k₁ k₂ λ {x} →
    adequate′ tt (k₁ x) (k₂ x) i (cong (_$ x) (impure-injectiveʳ eq))
 
  adequate : Adequate AbortHandler AbortTheory 
  adequate = sep-adequate AbortHandler AbortTheory adequate′

  correct : Correct AbortTheory AbortHandler 
  correct (here refl) = refl

  handle-abort : (σ : Abort ∙ ε ≈ ε′) → handleAbort {A = A} σ (abort ⦃ _ , σ ⦄) ≡ pure nothing
  handle-abort {ε} σ =
    begin
      handleAbort σ abort
    ≡⟨⟩ 
      handle AbortHandler σ tt abort
    ≡⟨⟩
      handle AbortHandler σ tt (♯ (impure ⟨ `abort , ⊥-elim ⟩))
    ≡⟨⟩
      handle′ AbortHandler tt (separate σ (impure (inj ⟨ `abort , (λ x → fold-free pure inject (⊥-elim x)) ⟩)))
    ≡⟨⟩
      handle′ AbortHandler tt (fold-free pure (λ where .αᶜ → impure ∘ proj σ) $ impure (inj ⟨ `abort , (λ x → fold-free pure inject (⊥-elim x)) ⟩))
    ≡⟨⟩ 
      handle′ AbortHandler tt (impure (proj σ (fmap (separate σ) (inj ⟨ `abort , ((λ x → fold-free pure inject (⊥-elim x))) ⟩)))) 
    ≡⟨ cong (handle′ AbortHandler tt ∘ impure ∘ proj σ)
       ( sym (inj-natural .commute {f = separate σ} _)
       ) ⟩
      handle′ AbortHandler tt (impure (proj σ (inj (⟨ (`abort , (λ x → separate σ $ fold-free pure inject (⊥-elim x))) ⟩)))) 
    ≡⟨ cong (handle′ AbortHandler tt ∘ impure)
         ( σ .union .equivalence _ .inverse .proj₂
           ( injˡ {C₁ = Abort} ε ⟨ (`abort , (λ x → separate σ $ fold-free pure inject (⊥-elim x))) ⟩)
         ) ⟩
    handle′ AbortHandler tt (impure (injˡ {C₁ = Abort} ε ⟨ (`abort , (λ x → separate σ $ fold-free pure inject (⊥-elim x))) ⟩)) 
    ≡⟨⟩ 
      pure nothing
    ∎
    where
      open Union
      open Inverse 
      open ≡-Reasoning
      instance inst : Abort ≲ _
      inst = _ , σ
  

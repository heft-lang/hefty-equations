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

open import Effect.Instance.Empty.Syntax

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
  
  impure-injectiveˡ :
    ∀ {ε} {c₁ c₂ : ε .shape} {k₁ : ε .position c₁ → Free ε A} {k₂ : ε .position c₂ → Free ε A}
    → impure ⟨ c₁ , k₁ ⟩ ≡ impure ⟨ c₂ , k₂ ⟩ → c₁ ≡ c₂
  impure-injectiveˡ refl = refl

  impure-injectiveʳ :
    ∀ {ε} {c : ε .shape} {k₁ k₂ : ε .position c → Free ε A}
    → impure ⟨ c , k₁ ⟩ ≡ impure ⟨ c , k₂ ⟩ → k₁ ≡ k₂ 
  impure-injectiveʳ refl = refl

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

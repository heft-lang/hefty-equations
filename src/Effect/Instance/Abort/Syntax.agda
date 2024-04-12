{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Container
open import Core.Ternary

open import Effect.Base
open import Effect.Syntax.Free
open import Effect.Theory.FirstOrder

open import Effect.Relation.Binary.FirstOrderInclusion
open import Effect.Relation.Ternary.FirstOrderSeparation

open import Data.Empty
open import Data.Product

open import Relation.Binary.PropositionalEquality

module Effect.Instance.Abort.Syntax where

data AbortC : Set where `abort : AbortC 

Abort : Container
Abort = record
  { shape    = AbortC
  ; position = λ where `abort → ⊥
  }

abort : ⦃ Abort ≲ ε ⦄ → Free ε A
abort = ♯ (impure ⟨ `abort , ⊥-elim ⟩)

abort-resp-⇔≲ : ∀ {A} (i₁ i₂ : Abort ≲ ε) → i₁ ⇔≲ i₂ → abort {A = A} ⦃ i₁ ⦄ ≡ abort ⦃ i₂ ⦄
abort-resp-⇔≲ i₁ i₂ eqv =
  begin
    abort ⦃ i₁ ⦄
  ≡⟨⟩ 
    ♯ ⦃ i₁ ⦄ (impure ⟨ `abort , ⊥-elim ⟩) 
  ≡⟨ ♯-resp-⇔≲ eqv (impure ⟨ `abort , ⊥-elim ⟩) ⟩
    ♯ ⦃ i₂ ⦄ (impure ⟨ `abort , ⊥-elim ⟩) 
  ≡⟨⟩ 
    abort ⦃ i₂ ⦄
  ∎
  where open ≡-Reasoning

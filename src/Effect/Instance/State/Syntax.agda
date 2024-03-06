{-# OPTIONS --without-K #-} 

open import Core.Container

open import Effect.Base
open import Effect.Separation
open import Effect.Inclusion
open import Effect.Theory.FirstOrder

open import Effect.Syntax.Free

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality

module Effect.Instance.State.Syntax (S : Set) where


data StateC (S : Set) : Set where
  `get : StateC S
  `put : S → StateC S

State : Container
State = record
  { shape    = StateC S
  ; position = λ where `get     → S
                       (`put _) → ⊤
  }

get : ⦃ State ≲ ε ⦄ → Free ε S
get = ♯ (impure ⟨ `get , pure ⟩)

get-resp-⇔≲ : (i₁ i₂ : State ≲ ε) → i₁ ⇔≲ i₂ → get ⦃ i₁ ⦄ ≡ get ⦃ i₂ ⦄
get-resp-⇔≲ _ _ eqv = ♯-resp-⇔≲ eqv (impure ⟨ `get , pure ⟩)

put : ⦃ State ≲ ε ⦄ → S → Free ε ⊤
put s = ♯ (impure ⟨ `put s , pure ⟩)

put-resp-⇔≲ : {s : S} (i₁ i₂ : State ≲ ε) → i₁ ⇔≲ i₂ → put ⦃ i₁ ⦄ s ≡ put ⦃ i₂ ⦄ s 
put-resp-⇔≲ _ _ eqv = ♯-resp-⇔≲ eqv (impure ⟨ `put _ , pure ⟩) 

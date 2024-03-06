{-# OPTIONS --without-K #-} 

open import Core.Container

open import Effect.Base
open import Effect.Inclusion
open import Effect.Syntax.Free 
open import Effect.Theory.FirstOrder

open import Data.Product

open import Relation.Binary.PropositionalEquality

module Effect.Instance.Reader.Syntax (R : Set) where 

data ReaderC : Set where
  `ask : ReaderC

Reader : Container
Reader = record
  { shape    = ReaderC
  ; position = λ where `ask → R
  }

ask : ⦃ Reader ≲ ε ⦄ → Free ε R
ask = ♯ (impure ⟨ `ask , pure ⟩) 

ask-resp-⇔≲ : (i₁ i₂ : Reader ≲ ε) → i₁ ⇔≲ i₂ → ask ⦃ i₁ ⦄ ≡ ask ⦃ i₂ ⦄
ask-resp-⇔≲ i₁ i₂ eqv = ♯-resp-⇔≲ eqv (impure ⟨ `ask , pure ⟩)

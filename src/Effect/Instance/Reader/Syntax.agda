{-# OPTIONS --without-K #-} 

open import Core.Container

open import Effect.Base
open import Effect.Inclusion
open import Effect.Syntax.Free 

open import Data.Product

module Effect.Instance.Reader.Syntax where 

data ReaderC : Set where
  `ask : ReaderC

Reader : (R : Set) → Container
Reader R = record
  { shape    = ReaderC
  ; position = λ where `ask → R
  }

ask : ∀ {R} → ⦃ Reader R ≲ ε ⦄ → Free ε R
ask = ♯ (impure ⟨ `ask , pure ⟩) 


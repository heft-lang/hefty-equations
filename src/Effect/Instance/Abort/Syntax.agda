open import Core.Functor
open import Core.Container

open import Free.Base
open import Effect.Base
open import Effect.Separation

open import Data.Empty
open import Data.Product

module Effect.Instance.Abort.Syntax where

data AbortC : Set where `abort : AbortC 

Abort : Container
Abort = record
  { shape    = AbortC
  ; position = λ where `abort → ⊥
  }



abort : ⦃ Abort ≲ ε ⦄ → Free ε A
abort = ♯ (impure ⟨ `abort , (λ()) ⟩)

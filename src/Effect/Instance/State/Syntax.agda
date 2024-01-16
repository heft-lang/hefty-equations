open import Core.Container

open import Effect.Base
open import Effect.Separation
open import Effect.Inclusion

open import Effect.Syntax.Free

open import Data.Unit
open import Data.Product

module Effect.Instance.State.Syntax where

variable S : Set 

data StateC (S : Set) : Set where
  `get : StateC S
  `put : S → StateC S

State : (S : Set) → Container
State S = record
  { shape    = StateC S
  ; position = λ where `get     → S
                       (`put _) → ⊤
  }

get : ⦃ State S ≲ ε ⦄ → Free ε S
get = ♯ (impure ⟨ `get , pure ⟩)

put : ⦃ State S ≲ ε ⦄ → S → Free ε ⊤
put s = ♯ (impure ⟨ `put s , pure ⟩)

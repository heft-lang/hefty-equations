open import Core.Functor
open import Core.Container
open import Core.Extensionality

open import Effect.Base
open import Free.Base 

open import Data.Unit
open import Data.Maybe hiding (_>>=_)
open import Data.Product
open import Data.Vec

open import Function 

open import Effect.Theory.FirstOrder

open import Effect.Instance.Abort.Syntax
open import Effect.Instance.Abort.Theory

open import Effect.Instance.Empty.Syntax

open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality

module Effect.Instance.Abort.Handler where 

AbortHandler : Handler Abort ⊤ Maybe A
AbortHandler = record
  { gen = λ x _ → just x
  ; hdl = record
    { αᶜ = λ where ⟨ `abort , _ ⟩ tt → return nothing
    }
  } 

handleAbort : Free (Abort ⊕ᶜ ε) A → Free ε (Maybe A)
handleAbort m = handle AbortHandler m tt


module Adequacy where 

  -- TODO: rephrase as general property of handlers
  adequacy : handleAbort {ε = Empty} (♯ᴱ c₁) ≡ handleAbort (♯ᴱ c₂) → c₁ ≈⟨ AbortTheory ⟩ c₂ 
  adequacy {c₁ = pure x                } {pure .x                     } refl = ≈-refl
  adequacy {c₁ = pure x                } {impure ⟨ `abort , _ ⟩       } ()
  adequacy {c₁ = impure ⟨ `abort , _ ⟩ } {pure x₁                     } ()
  adequacy {c₁ = impure ⟨ `abort , k₁ ⟩} {c₂ = impure ⟨ `abort , k₂ ⟩ } refl =
    begin
      impure ⟨ `abort , k₁ ⟩
    ≈⟪ ≡-to-≈ (cong (λ □ → impure ⟨ `abort , □ ⟩) ( extensionality λ() ) ) ⟫
      abort >>= k₁
    ≈⟪ ≈-eq′ bind-abort (here refl) ⟫
      abort
    ≈⟪ ≈-sym (≈-eq′ bind-abort (here refl)) ⟫
      abort >>= k₂
    ≈⟪ ≈-sym (≡-to-≈ (cong (λ □ → impure ⟨ `abort , □ ⟩) ( extensionality λ() ) )) ⟫ 
      impure ⟨ `abort , k₂ ⟩ 
    ∎ 
    where open ≈-Reasoning AbortTheory

AbortHandlerCorrect : Correct {A = A} AbortTheory AbortHandler 
AbortHandlerCorrect (here refl) {_ ∷ _ ∷ []} = refl

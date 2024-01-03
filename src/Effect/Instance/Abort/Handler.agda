open import Core.Functor
open import Core.Container
open import Core.Extensionality
open import Core.DisjointUnion

open import Effect.Base
open import Effect.Handle
open import Effect.Separation
open import Free.Base 

open import Data.Unit
open import Data.Maybe hiding (_>>=_)
open import Data.Product
open import Data.Vec
open import Data.Sum

open import Function 

open import Effect.Theory.FirstOrder

open import Effect.Instance.Abort.Syntax
open import Effect.Instance.Abort.Theory

open import Effect.Instance.Empty.Syntax

open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])


open import Core.MonotonePredicate Effect _≲_

module Effect.Instance.Abort.Handler where 

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

  open Inverse
  open DisjointUnion

  instance maybe-pointed : Pointed Maybe 
  maybe-pointed .point = just 

  modular : Modular AbortHandler
  modular = handle-modular AbortHandler 

  -- TODO: rephrase as general property of handlers
  --
  -- TODO: 
  adequacy : (m₁ m₂ : Free ε′ A)
           → (σ : Abort ∙ ε ≈ ε′)
           → handleAbort σ m₁ ≡ handleAbort σ m₂
           → m₁ ≈⟨ weaken (≲-∙-left σ) AbortTheory ⟩ m₂
  adequacy = {!!} 
--   adequacy {c₁ = pure x                } {pure .x                     } refl = ≈-refl
--   adequacy {c₁ = pure x                } {impure ⟨ `abort , _ ⟩       } ()
--   adequacy {c₁ = impure ⟨ `abort , _ ⟩ } {pure x₁                     } ()
--   adequacy {c₁ = impure ⟨ `abort , k₁ ⟩} {c₂ = impure ⟨ `abort , k₂ ⟩ } refl =
--     begin
--       impure ⟨ `abort , k₁ ⟩
--     ≈⟪ ≡-to-≈ (cong (λ □ → impure ⟨ `abort , □ ⟩) ( extensionality λ() ) ) ⟫
--       abort >>= k₁
--     ≈⟪ ≈-eq′ bind-abort (here refl) ⟫
--       abort
--     ≈⟪ ≈-sym (≈-eq′ bind-abort (here refl)) ⟫
--       abort >>= k₂
--     ≈⟪ ≈-sym (≡-to-≈ (cong (λ □ → impure ⟨ `abort , □ ⟩) ( extensionality λ() ) )) ⟫ 
--       impure ⟨ `abort , k₂ ⟩ 
--     ∎ 
--     where open ≈-Reasoning AbortTheory


-- -- AbortHandlerCorrect : Correct {A = A} AbortTheory AbortHandler 
-- -- AbortHandlerCorrect (here refl) {_ ∷ _ ∷ []} = refl

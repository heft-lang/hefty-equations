open import Core.Functor

open import Effect.Base
open import Free.Base

open import Effect.Theory.FirstOrder
open import Effect.Instance.Abort.Syntax

open import Data.Vec
open import Data.List

module Effect.Instance.Abort.Theory where

bind-abort : Equation Abort 2 (λ where (A ∷ B ∷ []) → A → Free Abort B) λ where (A ∷ B ∷ []) → B 
bind-abort = (λ where (_ ∷ _ ∷ []) k → abort >>= k) ≗ λ _ _ → abort 

AbortTheory : Theory Abort
AbortTheory =
  ∥ ◆ bind-abort
  ∷ [] ∥ 

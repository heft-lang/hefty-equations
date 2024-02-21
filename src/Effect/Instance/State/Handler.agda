{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Container
open import Core.Extensionality

open import Effect.Base
open import Effect.Separation
open import Effect.Syntax.Free

open import Data.Unit
open import Data.Maybe hiding (_>>=_)
open import Data.Product
open import Data.Vec

open import Function 

open import Effect.Handle
open import Effect.Theory.FirstOrder

open import Effect.Instance.State.Syntax
open import Effect.Instance.State.Theory

open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality

module Effect.Instance.State.Handler where 

StateHandler : Handler (State S) S (S ×_)
StateHandler = record
  { gen = flip _,_
  ; hdl = record
    { αᶜ = λ where ⟨ `get    , k ⟩ s → k s s
                   ⟨ `put s′ , k ⟩ _ → k tt s′
    }
  } 

open Handler

handleState : State S ∙ ε ≈ ε′ → Free ε′ A → S → Free ε (S × A)
handleState σ m s = handle StateHandler σ s m 

StateHandlerCorrect : Correct StateTheory (StateHandler {S = S})
StateHandlerCorrect (here refl)                              = refl
StateHandlerCorrect (there (here refl))                      = refl
StateHandlerCorrect (there (there (here refl)))              = refl
StateHandlerCorrect (there (there (there (here refl))))      = refl


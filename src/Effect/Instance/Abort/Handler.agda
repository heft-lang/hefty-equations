open import Core.Functor
open import Core.Container

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

AbortHandlerCorrect : Correct {A = A} AbortTheory AbortHandler 
AbortHandlerCorrect (here refl) {_ ∷ _ ∷ []} = refl

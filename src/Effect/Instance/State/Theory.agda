open import Core.Functor

open import Effect.Base
open import Free.Base

open import Effect.Theory.FirstOrder
open import Effect.Instance.State.Syntax

open import Data.Vec
open import Data.List
open import Data.Unit
open import Data.Product

module Effect.Instance.State.Theory where

get-get : Equation (State S) 1 (λ where (A ∷ []) → S → S → Free (State S) A) λ where (A ∷ []) → A
get-get =
  (λ where (_ ∷ []) k → get >>= λ s → get >>= k s) ≗ (λ where (_ ∷ []) k → get >>= λ s → k s s ) 

get-put : Equation (State S) 0 (λ where [] → ⊤) λ where [] → ⊤
get-put = (λ where [] tt → get >>= put) ≗ (λ where [] tt → return tt) 

put-get : Equation (State S) 0 (λ where [] → S) λ where [] → S
put-get = (λ where [] s → put s >> get) ≗ λ where [] s → put s >> return s 

put-put : Equation (State S) 0 (λ where [] → S × S) λ where [] → ⊤
put-put = (λ where [] (s , s′) → put s >> put s′) ≗ λ where [] (s , s′) → put s′ 

StateTheory : Theory (State S)
StateTheory =
  ∥ ◆ get-get
  ∷ ◆ put-get
  ∷ ◆ get-put
  ∷ ◆ put-put
  ∷ [] ∥ 
  

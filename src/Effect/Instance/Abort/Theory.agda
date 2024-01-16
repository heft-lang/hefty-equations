open import Core.Functor

open import Relation.Unary

open import Effect.Base
open import Effect.Syntax.Free
open import Effect.Separation
open import Effect.Inclusion 
open import Effect.Logic

open import Effect.Theory.FirstOrder
open import Effect.Instance.Abort.Syntax

open import Data.Product 
open import Data.List

module Effect.Instance.Abort.Theory where

open Connectives

bind-abort : □ Equation Abort 
bind-abort = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄  
  
  where
    module _ {ε} ⦃ _ : Abort ≲ ε ⦄ where 

      ctx ret : TypeContext 2 → Set
      ctx (A , B , _) = A → Free ε B
      ret (A , B , _) = B 
      left right : Π[ ctx ⇒ ret ⊢ Free ε ] 

      left  _ k = abort >>= k
      right _ _ = abort 

AbortTheory : Theory Abort
AbortTheory =
  ∥ bind-abort
  ∷ [] ∥ 

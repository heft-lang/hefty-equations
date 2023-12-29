open import Core.Functor

open import Relation.Unary

open import Effect.Base
open import Free.Base
open import Effect.Separation

open import Effect.Theory.FirstOrder
open import Effect.Instance.Abort.Syntax

open import Data.Product 
open import Data.List

module Effect.Instance.Abort.Theory where

bind-abort : Equation Abort 
bind-abort = exˡ ≗ exʳ
  
  where
    ctx ret : TypeContext 2 → Set
    ctx (A , B , _) = A → Free Abort B
    ret (A , B , _) = B 
    exˡ exʳ : Π[ ctx ⇒ ret ⊢ Free Abort ] 

    exˡ _ k = abort >>= k
    exʳ _ _ = abort 

AbortTheory : Theory Abort
AbortTheory =
  ∥ bind-abort
  ∷ [] ∥ 

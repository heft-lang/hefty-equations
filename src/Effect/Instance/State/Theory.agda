open import Core.Functor

open import Effect.Base
open import Effect.Syntax.Free

open import Effect.Theory.FirstOrder
open import Effect.Instance.State.Syntax
open import Effect.Logic
open import Effect.Inclusion 

open import Data.Vec
open import Data.List
open import Data.Unit
open import Data.Product

open import Relation.Unary

module Effect.Instance.State.Theory where

open Connectives

get-get : □ Equation (State S)
get-get = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄

  where
    module _ {ε} ⦃ _ : State S ≲ ε ⦄ where

      ctx ret : TypeContext 1 → Set
      ctx (A , _) = S → S → Free ε A
      ret (A , _) = A
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left  _ k = get >>= λ s → get >>= k s
      right _ k = get >>= λ s → k s s  


get-put : □ Equation (State S)
get-put = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄

  where 
    module _ {ε} ⦃ _ : State S ≲ ε ⦄ where

      ctx ret : TypeContext 0 → Set
      ctx _ = ⊤ 
      ret _ = ⊤
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left  _ _ = get >>= put 
      right _ _ = return tt


put-get : □ Equation (State S)
put-get = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄

  where 
    module _ {ε} ⦃ _ : State S ≲ ε ⦄ where

      ctx ret : TypeContext 0 → Set
      ctx _ = S 
      ret _ = S
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left  _ s = put s >> get 
      right _ s = put s >> return s


put-put : □ Equation (State S) 
put-put = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄ 

  where 
    module _ {ε} ⦃ _ : State S ≲ ε ⦄ where

      ctx ret : TypeContext 0 → Set
      ctx _ = S × S 
      ret _ = ⊤
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left  _ (s , s′) = put s >> put s′ 
      right _ (s , s′) = put s′


StateTheory : Theory (State S)
StateTheory =
  ∥ get-get
  ∷ get-put
  ∷ put-get 
  ∷ put-put
  ∷ [] ∥ 
  

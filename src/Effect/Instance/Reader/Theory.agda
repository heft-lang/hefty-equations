open import Core.Functor

open import Effect.Base
open import Effect.Syntax.Free
open import Effect.Logic
open import Effect.Inclusion 

open import Effect.Theory.FirstOrder
open import Effect.Instance.Reader.Syntax

open import Relation.Unary

open import Data.List
open import Data.Product

-- Effect theory for the reader effect, taken from 3MT
module Effect.Instance.Reader.Theory where

open Connectives

ask-query : ∀ {R} → □ Equation (Reader R)
ask-query = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄ 

  where
    module _ {R} {ε} ⦃ _ : Reader R ≲ ε ⦄ where

      ctx ret : TypeContext 1 → Set
      ctx (A , _) = Free ε A
      ret (A , _) = A
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left _  k = ask >> k
      right _ k = k 
      

ask-ask : ∀ {R} → □ Equation (Reader R) 
ask-ask = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄

  where
    module _ {R} {ε} ⦃ _ : Reader R ≲ ε ⦄ where

      ctx ret : TypeContext 1 → Set
      ctx (A , _) = R → R → Free ε A
      ret (A , _) = A
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left  _ k = ask >>= λ r → ask >>= k r
      right _ k = ask >>= λ r → k r r 


ask-bind : ∀ {R} → □ Equation (Reader R)
ask-bind = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄ 

  where
    module _ {R} {ε} ⦃ _ : Reader R ≲ ε ⦄ where

      ctx ret : TypeContext 2 → Set
      ctx (A , B , _) = Free ε A × (A → R → Free ε B)
      ret (A , B , _) = B
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left  _ (m , k) = m >>= λ x → ask >>= λ r → k x r 
      right _ (m , k) = ask >>= λ r → m >>= λ x → k x r 

ReaderTheory : ∀ {R} → Theory (Reader R)
ReaderTheory =
  ∥ ask-query 
  ∷ ask-ask
  ∷ ask-bind 
  ∷ [] ∥ 


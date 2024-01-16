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

module Effect.Instance.Reader.Theory where

open Connectives

-- ask >>= λ r → ask >>= k r ≡ ask >>= λ r → k r r 
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
      
ReaderTheory : ∀ {R} → Theory (Reader R)
ReaderTheory =
  ∥ ask-ask
  ∷ [] ∥ 


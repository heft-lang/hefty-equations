{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Functor.Monad
open import Core.Extensionality

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
open import Data.Sum

open import Data.List.Relation.Unary.All
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)

module Effect.Instance.Abort.Theory where

open Connectives
open Respects-⇔≲
open _⇔≲_

bind-abort : □ Equation Abort 
bind-abort = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄  
  
  where

    module _ {ε} where 

      ctx ret : TypeContext 2 → Set
      ctx (A , B , _) = A → Free ε B
      ret (A , B , _) = B 

      module _ ⦃ _ : Abort ≲ ε ⦄ where 
        left right : Π[ ctx ⇒ ret ⊢ Free ε ] 
        left  _ k = abort >>= k
        right _ _ = abort

bind-abort-respects-⇔≲ : Respects-⇔≲ bind-abort
bind-abort-respects-⇔≲ =
  eq-lawful
    (λ i₁ i₂ eqv → >>=-resp-⇔≲ eqv (λ i → abort ⦃ i ⦄) _ (abort-resp-⇔≲ i₁ i₂ eqv) λ _ → refl)
    (λ i₁ i₂ eqv → abort-resp-⇔≲ i₁ i₂ eqv)  

AbortTheory : Theory Abort
AbortTheory =
  ∥ bind-abort
  ∷ []
  ∣ bind-abort-respects-⇔≲ ∷ []
  ∥



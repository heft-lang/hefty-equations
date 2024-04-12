{-# OPTIONS --without-K --allow-unsolved-metas #-} 

open import Core.Functor
open import Core.Functor.Monad
open import Core.Extensionality
open import Core.Ternary
open import Core.Logic

open import Effect.Relation.Binary.FirstOrderInclusion
open import Effect.Relation.Ternary.FirstOrderSeparation
open import Effect.Base
open import Effect.Syntax.Free
open import Effect.Theory.FirstOrder
open import Effect.Instance.Abort.Syntax

open import Data.Product 
open import Data.List
open import Data.Sum
open import Data.List.Relation.Unary.All

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)
open import Relation.Unary


module Effect.Instance.Abort.Theory where

open Respects-⇔≲
open _⇔≲_

module _ {ε : Effect} ⦃ _ : Abort ≲ ε ⦄ where 

  bind-abort : Equation ε
  Δ′  bind-abort             = 2
  Γ′  bind-abort (A , B , _) = A → Free ε B
  R′  bind-abort (A , B , _) = B
  lhs bind-abort _ k         = abort >>= k
  rhs bind-abort _ k         = abort

 
AbortTheory : ExtensibleTheory Abort
theory AbortTheory = nec ∥ bind-abort ∷ [] ∥
respects-⇔≲ (lawful AbortTheory) i₁ i₂ eq = {!!}


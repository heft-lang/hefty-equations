{-# OPTIONS --without-K --type-in-type #-} 

open import Core.Functor
open import Core.Functor.Monad
open import Core.Ternary
open import Core.Logic

open import Effect.Base
open import Effect.Syntax.Hefty

open import Effect.Theory.FirstOrder
open import Effect.Theory.HigherOrder

open import Effect.Relation.Binary.FirstOrderInclusion
open import Effect.Relation.Ternary.FirstOrderSeparation
open import Effect.Relation.Binary.HigherOrderInclusion
open import Effect.Relation.Ternary.HigherOrderSeparation

open import Data.Vec
open import Data.List
open import Data.Unit
open import Data.Bool
open import Data.Product

open import Function
open import Relation.Unary

module Effect.Instance.Lambda.Theory
  (c : Set → Set)
  (_[_]↦_ : Set → Effect → Set → Set)
  ⦃ _ : Pointed c ⦄ where

open import Effect.Instance.Lambda.Syntax c _[_]↦_

module _ {η : Effectᴴ} ⦃ i : Lam ≲ η ⦄ where 

  beta : Equationᴴ η
  Δ′   beta               = 2
  Γ′   beta ε (A , B , _) = (c A → Hefty (η ε) B) × Hefty (η ε) A
  R′   beta ε (A , B , _) = B
  lhsᴴ beta _ (f , m)     = abs f >>= λ f′ → app f′ m
  rhsᴴ beta _ (f , m)     = m >>= f ∘ point

  eta : Equationᴴ η
  Δ′   eta = 2
  Γ′   eta ε (A , B , _) = c A [ ε ]↦ B
  R′   eta ε (A , B , _) = c A [ ε ]↦ B 
  lhsᴴ eta _ f = pure f
  rhsᴴ eta _ f = abs λ x → app f (var x)
  
LambdaTheory : Theoryᴴ Lam
arity LambdaTheory = Bool
eqs LambdaTheory false = nec beta
eqs LambdaTheory true  = nec eta



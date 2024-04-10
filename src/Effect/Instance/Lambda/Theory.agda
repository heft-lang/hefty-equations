{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Functor.Monad

open import Effect.Base
open import Effect.Syntax.Hefty

open import Effect.Theory.FirstOrder
open import Effect.Theory.HigherOrder

open import Data.Vec
open import Data.List
open import Data.Unit
open import Data.Product

open import Function
open import Relation.Unary

module Effect.Instance.Lambda.Theory
  (c : Set → Set)
  (_[_]↦_ : Set → Effect → Set → Set)
  ⦃ _ : Pointed c ⦄ where

open import Effect.Instance.Lambda.Syntax c _[_]↦_

instance ⊑-refl-inst : Lam ε ⊑ Lam ε
⊑-refl-inst = ⊑-refl

beta : Equationᴴ Lam
beta = left ≗ᴴ right 

  where
    ctx ret : Effect → TypeContext 2 → Set
    ctx ε (A , B , _) = (c A → Hefty (Lam ε) B) × Hefty (Lam ε) A
    ret ε (A , B , _) = B
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (Lam ε) ]

    left  _ (f , m) = abs f >>= λ f′ → app f′ m
    right _ (f , m) = m >>= f ∘ point 


eta : Equationᴴ Lam 
eta = left ≗ᴴ right 

  where
    ctx ret : Effect → TypeContext 2 → Set
    ctx ε (A , B , _) = c A [ ε ]↦ B
    ret ε (A , B , _) = c A [ ε ]↦ B
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (Lam ε) ]

    left _  f = pure f
    right _ f = abs λ x → app f (var x)

LambdaTheory : Theoryᴴ Lam
LambdaTheory =
  ∥ beta
  ∷ eta
  ∷ [] ∥ᴴ 


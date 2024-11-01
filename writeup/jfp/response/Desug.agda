{-# OPTIONS --type-in-type #-}
module Desug where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum

open import tex.sections.2-algebraic-effects

open FreeModule
open Effect

open import Data.Product

data Prog (Δ γ : Effect) (A : Set) : Set where
  return  : A                                                → Prog Δ γ A
  call    : ⟦ Δ ⟧ (Prog Δ γ A)                                → Prog Δ γ A
  enter   : {B : Set} → ⟦ γ ⟧ (Prog Δ γ B) → (B → Prog Δ γ A) → Prog Δ γ A

data ScopedOp (Ref : Set → Set) (γ : Effect) : Set where
  sub-scope : Set → Op γ → ScopedOp Ref γ
  sub-end   : (B : Set) → Ref B → B → ScopedOp Ref γ

conv-Effect : Effect → (Set → Set) → Effect
Op (conv-Effect Δ Ref) = ScopedOp Ref Δ
Ret (conv-Effect Δ Ref) (sub-scope B o) = Ref B × Ret Δ o -- Scope
                                        ⊎ B -- Continuation
Ret (conv-Effect Δ Ref) (sub-end _ _ _) = ⊥

convert : {A : Set} {γ : Effect} (Ref : Set → Set)
        → Prog Δ γ A
        → Free (conv-Effect γ Ref ⊕ Δ) A
convert Ref (return x) = pure x
convert Ref (call (o , k)) = impure (inj₂ o , λ x → convert Ref (k x))
convert Ref (enter {B = B} (o , k₁) k₂) = impure (inj₁ (sub-scope B o) , λ where
  (inj₁ (c , r)) → convert Ref (k₁ r) FreeModule.𝓑 λ b → impure (inj₁ (sub-end B c b) , ⊥-elim)
  (inj₂ y) → convert Ref (k₂ y))


{-# OPTIONS --type-in-type --without-K #-}

open import Core.Functor
open import Core.Signature
open import Core.Ternary

open import Effect.Base
open import Effect.Syntax.Hefty
open import Effect.Relation.Binary.HigherOrderInclusion
open import Effect.Relation.Ternary.HigherOrderSeparation

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])

module Effect.Instance.Lambda.Syntax (c : Set → Set) (_[_]↦_ : Set → Effect → Set → Set) where 

data LamC (ε : Effect) : Set where
  `var : c A   → LamC ε
  `abs : {A B : Set} → LamC ε
  `app : (c A [ ε ]↦ B) → LamC ε

Lam : Effectᴴ
Lam ε = record
  { command = LamC ε
  ; response = λ where
      (`var {A} _    ) → A
      (`abs {A} {B}  ) → c A [ ε ]↦ B
      (`app {A} {B} _) → B
  ; fork = λ where
      (`var _)       → ⊥
      (`abs {A} {B}) → c A
      (`app x)       → ⊤
  ; returns = λ where
    {`abs {A} {B}  } x  → B
    {`app {A} {B} _} tt → A
  } 

var : ⦃ Lam ≲ η ⦄ → c A → Hefty (η ε) A 
var x = impure (injᴴ ⟪ `var x , pure , (λ()) ⟫) 

abs : ⦃ Lam ≲ η ⦄ → (c A → Hefty (η ε) B) → Hefty (η ε) (c A [ ε ]↦ B) 
abs f = impure (injᴴ ⟪ `abs , pure , f  ⟫)

app :  ⦃ Lam ≲ η ⦄ → (c A [ ε ]↦ B) → Hefty (η ε) A → Hefty (η ε) B
app f m = impure (injᴴ ⟪ `app f , pure , (λ where tt → m) ⟫)



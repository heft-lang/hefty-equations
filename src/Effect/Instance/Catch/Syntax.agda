{-# OPTIONS --without-K --type-in-type #-}

open import Core.Functor
open import Core.Signature
open import Core.Ternary

open import Effect.Base
open import Effect.Syntax.Hefty

open import Effect.Relation.Ternary.HigherOrderSeparation
open import Effect.Relation.Binary.HigherOrderInclusion

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Function 

open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])

module Effect.Instance.Catch.Syntax where

data CatchC : Set where
  `throw : CatchC
  `catch : (t : Set) → CatchC
  
Catch : Effect → Signature 
Catch _ = record
  { command  = CatchC
  ; response = λ where (`catch t) → t
                       `throw     → ⊥ 
  ; fork     = λ where (`catch A) → ⊤ ⊎ ⊤
                       `throw     → ⊥ 
  ; returns  = λ where {(`catch A)} → [ (λ where tt → A) , (λ where tt → A) ]
  }

throw : ⦃ Catch ≲ η ⦄ → Hefty (η ε) A
throw = ♯ᴴ (impure ⟪ `throw , (λ()) , (λ()) ⟫)

catch : ⦃ Catch ≲ η ⦄ → Hefty (η ε) A → Hefty (η ε) A → Hefty (η ε) A 
catch m₁ m₂ = impure (injᴴ ⟪ `catch _ , pure , [ const m₁ , const m₂ ] ⟫)

   

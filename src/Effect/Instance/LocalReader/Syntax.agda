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

module Effect.Instance.LocalReader.Syntax (R : Set) where

data LocalReaderC : Set where
  `ask   : LocalReaderC
  `local : (t : Set) (f : R → R) → LocalReaderC


LocalReader : Effect → Signature
LocalReader _ = record
  { command  = LocalReaderC
  ; response = λ where `ask         → R
                       (`local t f) → t
  ; fork     = λ where `ask         → ⊥
                       (`local t f) → ⊤  
  ; returns  = λ where {`local t f} tt → t
  }

askl : ⦃ LocalReader ≲ η ⦄ → Hefty (η ε) R
askl = ♯ᴴ (impure ⟪ `ask , pure , (λ()) ⟫)

local : ⦃ LocalReader ≲ η ⦄ → (R → R) → Hefty (η ε) A → Hefty (η ε) A
local f m = impure (injᴴ ⟪ `local _ f , pure , (λ where tt → m) ⟫) 


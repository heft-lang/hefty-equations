{-# OPTIONS --type-in-type --without-K #-} 

open import Core.Functor
open import Core.Signature 

open import Effect.Base
open import Effect.Syntax.Hefty

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

askl : ⦃ LocalReader ε ⊑ᴴ η ⦄ → Hefty η R
askl = ♯ᴴ (impure ⟪ `ask , pure , (λ()) ⟫)

local : ⦃ LocalReader ε ⊑ᴴ η ⦄ → (R → R) → Hefty η A → Hefty η A
local {ε} {η} {A} f m = impure
  ⟪ injᴴ-c (`local A f)
  , pure ∘ subst id (sym response-stable)
  , (subst (Hefty η) types-stable ∘ λ where tt → m) ∘ subst id (sym fork-stable)
  ⟫


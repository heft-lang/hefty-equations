{-# OPTIONS --type-in-type #-}

module Core.Extensionality where

open import Level
open import Axiom.Extensionality.Propositional

postulate
  extensionality : Extensionality zero zero

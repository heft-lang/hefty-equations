{-# OPTIONS --without-K #-}

module Core.Extensionality where

open import Level
open import Axiom.Extensionality.Propositional

postulate
  polymorphicExtensionality : ∀ a b → Extensionality a b 

extensionality = polymorphicExtensionality zero zero

extensionality′ : ExtensionalityImplicit zero zero
extensionality′ = implicit-extensionality extensionality 

pfext = polymorphicExtensionality

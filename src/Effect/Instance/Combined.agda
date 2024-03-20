{-# OPTIONS --without-K #-}

open import Effect.Elaborate

module Effect.Instance.Combined where

elab : Elaboration {!!} {!!} 
elab = {!!} 



_* : ∀[ □ (P ⇒ M Q) ] → ∀[ M P ⇒ M Q ]

curry   : ∀[ P ⇒ ◇ Q ] → ∀[ □ P ⇒ Q ]
uncurry : ∀[ □ P ⇒ Q ] → ∀[ P ⇒ ◇ Q ]


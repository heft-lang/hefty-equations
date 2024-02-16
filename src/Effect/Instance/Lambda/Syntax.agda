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

module Effect.Instance.Lambda.Syntax (c : Set → Set) (_[_]↦_ : Set → Effect → Set → Set) where 

data LamC (ε : Effect) : Set where
  `var : c A   → LamC ε
  `abs : {A B : Set} → LamC ε
  `app : (c A [ ε ]↦ B) → LamC ε

Lam : Effect → Signature
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


var : ⦃ Lam ε ⊑ᴴ η ⦄ → c A → Hefty η A 
var x = impure
  ⟪ injᴴ-c (`var x)
  , pure ∘ subst id (sym response-stable)
  , ⊥-elim ∘ subst id (sym fork-stable)
  ⟫

abs : ⦃ Lam ε ⊑ᴴ η ⦄ → (c A → Hefty η B) → Hefty η (c A [ ε ]↦ B) 
abs f = impure
  ⟪ injᴴ-c `abs
  , pure ∘ subst id (sym response-stable)
  , subst (Hefty _) (types-stable) ∘ f ∘ subst id (sym fork-stable)
  ⟫

app : ⦃ Lam ε ⊑ᴴ η ⦄ → (c A [ ε ]↦ B) → Hefty η A → Hefty η B
app f m = impure
  ⟪ injᴴ-c (`app f)
  , pure ∘ subst id (sym response-stable)
  , (λ _ → subst (Hefty _) types-stable m)
  ⟫ 


{-# OPTIONS --type-in-type #-}

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

module Effect.Instance.Catch.Syntax where

data CatchC : Set where
  `throw : CatchC
  `catch : (t : Set) → CatchC
  
Catch : Signature 
Catch = record
  { command  = CatchC
  ; response = λ where (`catch t) → t
                       `throw     → ⊥ 
  ; fork     = λ where (`catch A) → ⊤ ⊎ ⊤
                       `throw     → ⊥ 
  ; returns  = λ where {(`catch A)} → [ (λ where tt → A) , (λ where tt → A) ]
  }

throw : ⦃ Catch ⊑ᴴ η ⦄ → Hefty η A
throw = ♯ᴴ (impure ⟪ `throw , (λ()) , (λ()) ⟫)

match_·_on_ : ∀ {C : Set} → (f : A → B) (x : A) → ((Σ B λ y → f x ≡ y) → C) → C 
match f · x on g = g (f x , refl)

catch : ⦃ Catch ⊑ᴴ η ⦄ → Hefty η A → Hefty η A → Hefty η A 
catch {η}{A} m₁ m₂ = impure
  ⟪ injᴴ-c (`catch _)
  , pure ∘ subst id (sym response-stable) 
  , catch-subs 
  ⟫
  where
    catch-subs : (ψ : fork η (injᴴ-c (`catch A))) → Hefty η (returns η ψ) 
    catch-subs ψ
      with subst id (sym fork-stable) ψ
         | inspect (subst id (sym fork-stable)) ψ
    ... | inj₁ tt | ≡[ eq ]
      = subst (Hefty η)
          ( trans
              ( subst (λ □ → A ≡ Catch .returns □) (sym eq) refl )
              types-stable ) m₁
    ... | inj₂ tt | ≡[ eq ]
      = subst (Hefty η)
          ( trans
            ( subst (λ □ → A ≡ Catch .returns □) (sym eq) refl )
            types-stable ) m₂

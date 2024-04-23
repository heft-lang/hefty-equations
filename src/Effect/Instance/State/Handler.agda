{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Functor.Monad
open import Core.Functor.NaturalTransformation
open import Core.Container
open import Core.Extensionality
open import Core.Ternary
open import Core.Logic 

open import Effect.Base
open import Effect.Syntax.Free

open import Effect.Relation.Binary.FirstOrderInclusion
open import Effect.Relation.Ternary.FirstOrderSeparation

open import Data.Unit
open import Data.Maybe hiding (_>>=_)
open import Data.Product renaming (map to pmap)
open import Data.Vec
open import Data.Fin

open import Function 

open import Effect.Handle
open import Effect.Theory.FirstOrder

open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

open import Level

module Effect.Instance.State.Handler (S : Set) where 

open import Effect.Instance.State.Syntax S
open import Effect.Instance.State.Theory S

module _ where

  open ≡-Reasoning 

  ×-functor : Functor {a = 0ℓ} (S ×_)
  ×-functor = record
    { fmap    = λ f → pmap id f
    ; fmap-id = refl
    ; fmap-∘  = λ _ _ → refl
    } 

  instance stateT-functor : Functor (const S ⇒ (S ×_) ⊢ Free ε)
  stateT-functor = record
    { fmap    = λ f m s → fmap (pmap id f) (m s)
    ; fmap-id = extensionality
        λ m → cong (λ ○ s → ○ (m s)) (fmap-id {F = Free _})
    ; fmap-∘  = λ f g → extensionality
        λ m → cong (_∘ m) (fmap-∘ (pmap id f) (pmap id g))
    }

  instance stateT-monad : Monad (const S ⇒ (S ×_) ⊢ Free ε)
  stateT-monad = record
    { return         = curry (pure ∘ swap)
    ; _∗             = λ k m s → m s >>= uncurry k ∘ swap
    ; >>=-idˡ        = λ _ _ → refl
    ; >>=-idʳ        =
        λ m → extensionality λ s → >>=-idʳ (m s)
    ; >>=-assoc      =
        λ k₁ k₂ m
          → extensionality λ s →
              >>=-assoc
                (uncurry k₁ ∘ swap)
                (uncurry k₂ ∘ swap)
                (m s)
    ; return-natural = λ where
        .commute {f = f} x →
          cong (λ ○ s → fmap (s ,_) ○)
            (return-natural ⦃ free-monad ⦄ .commute {f = f} x) 
    } 

  StateHandler : Handler State S (S ×_)
  Handler.F-functor   StateHandler = ×-functor
  Handler.M-monad     StateHandler = stateT-monad
  
  Handler.hdl         StateHandler .αᶜ ⟨ `get , k ⟩    = λ s → k s s
  Handler.hdl         StateHandler .αᶜ ⟨ `put s′ , k ⟩ = λ _ → k tt s′
  
  Handler.M-apply     StateHandler                  = refl
  Handler.hdl-commute StateHandler f ⟨ `get   , k ⟩ = refl
  Handler.hdl-commute StateHandler f ⟨ `put _ , k ⟩ = refl


open Handler

handleState : State ∙ ε ≈ ε′ → Free ε′ A → S → Free ε (S × A)
handleState σ m s = handle StateHandler σ m s 

module Properties where 
 
  correct : Correct StateTheory StateHandler
  correct (zero                 , refl) = refl
  correct (suc zero             , refl) = refl
  correct (suc (suc zero)       , refl) = refl
  correct (suc (suc (suc zero)) , refl) = refl

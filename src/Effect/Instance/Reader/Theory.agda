{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Functor.Monad

open import Effect.Base
open import Effect.Syntax.Free
open import Effect.Logic
open import Effect.Inclusion 

open import Effect.Theory.FirstOrder

open import Relation.Unary

open import Data.List
open import Data.Product

open import Data.List.Relation.Unary.All

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)

-- Effect theory for the reader effect, taken from 3MT
module Effect.Instance.Reader.Theory (R : Set) where


open import Effect.Instance.Reader.Syntax R

open Connectives

ask-query : □ Equation Reader
ask-query = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄ 
  where
    module _ {ε} ⦃ _ : Reader ≲ ε ⦄ where
      ctx ret : TypeContext 1 → Set
      ctx (A , _) = Free ε A
      ret (A , _) = A
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left _  k = ask >> k
      right _ k = k 

ask-query-respects-⇔≲ : Respects-⇔≲ ask-query
ask-query-respects-⇔≲ = eq-lawful
  ( λ i₁ i₂ eqv →
      >>=-resp-⇔≲ eqv
        (λ i → ask ⦃ i ⦄) _
        (ask-resp-⇔≲ i₁ i₂ eqv)
        (λ _ → refl)
  ) (λ i₁ i₂ eqv → refl )

ask-ask : □ Equation Reader 
ask-ask = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄
  where
    module _ {ε} ⦃ _ : Reader ≲ ε ⦄ where
      ctx ret : TypeContext 1 → Set
      ctx (A , _) = R → R → Free ε A
      ret (A , _) = A
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left  _ k = ask >>= λ r → ask >>= k r
      right _ k = ask >>= λ r → k r r 

ask-ask-respects-⇔≲ : Respects-⇔≲ ask-ask
ask-ask-respects-⇔≲ = eq-lawful
  ( λ i₁ i₂ eqv →
      >>=-resp-⇔≲ eqv
        (λ i → ask ⦃ i ⦄)
        (λ i _ → ask ⦃ i ⦄ >>= _)
        (ask-resp-⇔≲ i₁ i₂ eqv)
        ( λ _ →
          >>=-resp-⇔≲ eqv
            (λ i → ask ⦃ i ⦄) _
            (ask-resp-⇔≲ i₁ i₂ eqv)
            (λ _ → refl)
        )
  ) ( λ i₁ i₂ eqv →
    >>=-resp-⇔≲ eqv
      (λ i → ask ⦃ i ⦄) _
      (ask-resp-⇔≲ i₁ i₂ eqv)
      (λ _ → refl)
  )

ask-bind : □ Equation Reader
ask-bind = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄ 
  where
    module _ {ε} ⦃ _ : Reader ≲ ε ⦄ where
      ctx ret : TypeContext 2 → Set
      ctx (A , B , _) = Free ε A × (A → R → Free ε B)
      ret (A , B , _) = B
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left  _ (m , k) = m >>= λ x → ask >>= λ r → k x r 
      right _ (m , k) = ask >>= λ r → m >>= λ x → k x r 

ask-bind-respects-⇔≲ : Respects-⇔≲ ask-bind
ask-bind-respects-⇔≲ = eq-lawful
  ( λ where
      i₁ i₂ {γ = m , k} eqv →
        >>=-resp-⇔≲ eqv
          (λ _ → m)
          (λ i _ → ask ⦃ i ⦄ >>= k _) refl
          (λ _ →
            >>=-resp-⇔≲ eqv
              (λ i → ask ⦃ i ⦄) _
              (ask-resp-⇔≲ i₁ i₂ eqv)
              (λ _ → refl)
          )
  ) ( λ where
    i₁ i₂ {γ = m , k} eqv →
      >>=-resp-⇔≲ eqv
        (λ i → ask ⦃ i ⦄) _
        (ask-resp-⇔≲ i₁ i₂ eqv)
        (λ _ → refl)
  ) 

ReaderTheory : Theory Reader
ReaderTheory =
  ∥ ask-query 
  ∷ ask-ask
  ∷ ask-bind 
  ∷ []
  ∣ ask-query-respects-⇔≲
  ∷ ask-ask-respects-⇔≲
  ∷ ask-bind-respects-⇔≲
  ∷ []
  ∥ 

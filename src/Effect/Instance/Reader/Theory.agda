{-# OPTIONS --without-K --allow-unsolved-metas #-} 

open import Core.Functor
open import Core.Functor.Monad
open import Core.Ternary
open import Core.Logic

open import Effect.Base
open import Effect.Syntax.Free

open import Effect.Theory.FirstOrder
open import Effect.Relation.Binary.FirstOrderInclusion

open import Relation.Unary

open import Data.List
open import Data.Product
open import Data.Fin

open import Data.List.Relation.Unary.All

open import Effect.Relation.Ternary.FirstOrderSeparation
open import Effect.Relation.Binary.FirstOrderInclusion

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)

-- Effect theory for the reader effect, taken from 3MT
module Effect.Instance.Reader.Theory (R : Set) where
 
open import Effect.Instance.Reader.Syntax R

module _ {ε : Effect} ⦃ _ : Reader ≲ ε ⦄ where

  ask-query : Equation ε
  Δ′  ask-query = 1
  Γ′  ask-query (A , _) = Free ε A
  R′  ask-query (A , _) = A
  lhs ask-query _ k    = ask >> k
  rhs ask-query _ k    = k

  ask-ask : Equation ε
  Δ′  ask-ask = 1
  Γ′  ask-ask (A , _) = R → R → Free ε A
  R′  ask-ask (A , _) = A
  lhs ask-ask _ k = ask >>= λ r → ask >>= k r
  rhs ask-ask _ k = ask >>= λ r → k r r

  ask-bind : Equation ε
  Δ′ ask-bind = 2
  Γ′ ask-bind (A , B , _) = Free ε A × (A → R → Free ε B)
  R′ ask-bind (A , B , _) = B
  lhs ask-bind _ (m , k) = m >>= λ x → ask >>= λ r → k x r
  rhs ask-bind _ (m , k) = ask >>= λ r → m >>= λ x → k x r

ReaderTheory : Theory Reader
arity ReaderTheory                = Fin 3
eqs ReaderTheory zero             = nec ask-query
eqs ReaderTheory (suc zero)       = nec ask-ask
eqs ReaderTheory (suc (suc zero)) = nec ask-bind
lawful ReaderTheory = {!!}

-- ask-query-respects-⇔≲ : Respects-⇔≲ ask-query
-- ask-query-respects-⇔≲ = eq-lawful
--   ( λ i₁ i₂ eqv →
--       >>=-resp-⇔≲ eqv
--         (λ i → ask ⦃ i ⦄) _
--         (ask-resp-⇔≲ i₁ i₂ eqv)
--         (λ _ → refl)
--   ) (λ i₁ i₂ eqv → refl )

-- ask-ask-respects-⇔≲ : Respects-⇔≲ ask-ask
-- ask-ask-respects-⇔≲ = eq-lawful
--   ( λ i₁ i₂ eqv →
--       >>=-resp-⇔≲ eqv
--         (λ i → ask ⦃ i ⦄)
--         (λ i _ → ask ⦃ i ⦄ >>= _)
--         (ask-resp-⇔≲ i₁ i₂ eqv)
--         ( λ _ →
--           >>=-resp-⇔≲ eqv
--             (λ i → ask ⦃ i ⦄) _
--             (ask-resp-⇔≲ i₁ i₂ eqv)
--             (λ _ → refl)
--         )
--   ) ( λ i₁ i₂ eqv →
--     >>=-resp-⇔≲ eqv
--       (λ i → ask ⦃ i ⦄) _
--       (ask-resp-⇔≲ i₁ i₂ eqv)
--       (λ _ → refl)
--   )

-- ask-bind-respects-⇔≲ : Respects-⇔≲ ask-bind
-- ask-bind-respects-⇔≲ = eq-lawful
--   ( λ where
--       i₁ i₂ {γ = m , k} eqv →
--         >>=-resp-⇔≲ eqv
--           (λ _ → m)
--           (λ i _ → ask ⦃ i ⦄ >>= k _) refl
--           (λ _ →
--             >>=-resp-⇔≲ eqv
--               (λ i → ask ⦃ i ⦄) _
--               (ask-resp-⇔≲ i₁ i₂ eqv)
--               (λ _ → refl)
--           )
--   ) ( λ where
--     i₁ i₂ {γ = m , k} eqv →
--       >>=-resp-⇔≲ eqv
--         (λ i → ask ⦃ i ⦄) _
--         (ask-resp-⇔≲ i₁ i₂ eqv)
--         (λ _ → refl)
--   ) 

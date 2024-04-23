{-# OPTIONS --without-K --allow-unsolved-metas #-} 

open import Core.Functor
open import Core.Functor.Monad

open import Core.Ternary
open import Core.Logic

open import Effect.Base
open import Effect.Syntax.Free

open import Effect.Theory.FirstOrder
open import Effect.Relation.Binary.FirstOrderInclusion
open import Effect.Relation.Ternary.FirstOrderSeparation

open import Data.Vec
open import Data.List
open import Data.Unit
open import Data.Product
open import Data.Fin

open import Relation.Unary
open import Data.List.Relation.Unary.All

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)

module Effect.Instance.State.Theory (S : Set) where

open import Effect.Instance.State.Syntax S

module _ {ε : Effect} ⦃ _ : State ≲ ε ⦄ where 

  get-get : Equation ε
  Δ′  get-get = 1
  Γ′  get-get (A , _) = S → S → Free ε A
  R′  get-get (A , _) = A
  lhs get-get _ k = get >>= λ s → get >>= k s
  rhs get-get _ k = get >>= λ s → k s s

  get-put : Equation ε
  Δ′ get-put = 0
  Γ′ get-put _ = ⊤
  R′ get-put _ = ⊤
  lhs get-put _ _ = get >>= put
  rhs get-put _ _ = return tt
 
  put-get : Equation ε
  Δ′ put-get = 0
  Γ′ put-get _ = S
  R′ put-get _ = S
  lhs put-get _ s = put s >> get
  rhs put-get _ s = put s >> return s

  put-put : Equation ε  
  Δ′ put-put = 0
  Γ′ put-put x = S × S
  R′ put-put _ = ⊤
  lhs put-put _ (s , s′) = put s >> put s′
  rhs put-put _ (s , s′) = put s′

StateTheory : Theory State
arity StateTheory = Fin 4
eqs StateTheory zero = nec get-get
eqs StateTheory (suc zero) = nec get-put
eqs StateTheory (suc (suc zero)) = nec put-get
eqs StateTheory (suc (suc (suc zero))) = nec put-put
lawful StateTheory = {!!}


-- 
-- get-get-respects-⇔≲ : Respects-⇔≲ get-get
-- get-get-respects-⇔≲ = eq-lawful
--   ( λ i₁ i₂ eqv →
--       >>=-resp-⇔≲ eqv
--         (λ i → get ⦃ i ⦄)
--         (λ i s → get ⦃ i ⦄ >>= _)
--         (get-resp-⇔≲ _ _ eqv)
--         ( λ s →
--             >>=-resp-⇔≲ eqv
--               (λ i → get ⦃ i ⦄) _
--               (get-resp-⇔≲ _ _ eqv)
--               (λ _ → refl)
--         )
--   ) ( λ i₁ i₂ eqv →
--       >>=-resp-⇔≲ eqv
--         (λ i → get ⦃ i ⦄) _
--         (get-resp-⇔≲ _ _ eqv)
--         (λ _ → refl)
--   ) 
--
-- get-put-respects-⇔≲ : Respects-⇔≲ get-put
-- get-put-respects-⇔≲ = eq-lawful
--   ( λ i₁ i₂ eqv →
--       >>=-resp-⇔≲ eqv
--         (λ i → get ⦃ i ⦄)
--         (λ i → put ⦃ i ⦄)
--         (get-resp-⇔≲ _ _ eqv)
--         (λ _ → put-resp-⇔≲ _ _ eqv)
--   ) (λ i₁ i₂ eqv → refl) 
--
-- 
-- put-get-respects-⇔≲ : Respects-⇔≲ put-get
-- put-get-respects-⇔≲ = eq-lawful
--   ( λ where
--       i₁ i₂ {γ = s} eqv →
--         >>=-resp-⇔≲ eqv
--           (λ i → put ⦃ i ⦄ s)
--           (λ i _ → get ⦃ i ⦄)
--           (put-resp-⇔≲ i₁ i₂ eqv)
--           (λ _ → get-resp-⇔≲ i₁ i₂ eqv)
--   ) ( λ where
--     i₁ i₂ {γ = s} eqv →
--       >>=-resp-⇔≲ eqv
--         (λ i → put ⦃ i ⦄ s)
--         (λ i _ → return s)
--         (put-resp-⇔≲ i₁ i₂ eqv)
--         (λ _ → refl)
--   )
-- 
-- put-put-respects-⇔≲ : Respects-⇔≲ put-put
-- put-put-respects-⇔≲ = eq-lawful
--   ( λ where
--       i₁ i₂ {γ = s , s′} eqv →
--         >>=-resp-⇔≲ eqv
--           (λ i → put ⦃ i ⦄ s)
--           (λ i _ → put ⦃ i ⦄ s′)
--           (put-resp-⇔≲ i₁ i₂ eqv)
--           (λ _ → put-resp-⇔≲ i₁ i₂ eqv)
--   ) (λ i₁ i₂ eqv → put-resp-⇔≲ i₁ i₂ eqv)
-- 

{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Functor.Monad

open import Effect.Base
open import Effect.Syntax.Free

open import Effect.Theory.FirstOrder
open import Effect.Logic
open import Effect.Inclusion 

open import Data.Vec
open import Data.List
open import Data.Unit
open import Data.Product

open import Relation.Unary
open import Data.List.Relation.Unary.All

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)

module Effect.Instance.State.Theory (S : Set) where


open import Effect.Instance.State.Syntax S

open Connectives

get-get : □ Equation (State S)
get-get = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄

  where
    module _ {ε} ⦃ _ : State S ≲ ε ⦄ where

      ctx ret : TypeContext 1 → Set
      ctx (A , _) = S → S → Free ε A
      ret (A , _) = A
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left  _ k = get >>= λ s → get >>= k s
      right _ k = get >>= λ s → k s s  

get-get-respects-⇔≲ : Respects-⇔≲ get-get
get-get-respects-⇔≲ = eq-lawful
  ( λ i₁ i₂ eqv →
      >>=-resp-⇔≲ eqv
        (λ i → get ⦃ i ⦄)
        (λ i s → get ⦃ i ⦄ >>= _)
        (get-resp-⇔≲ _ _ eqv)
        ( λ s →
            >>=-resp-⇔≲ eqv
              (λ i → get ⦃ i ⦄) _
              (get-resp-⇔≲ _ _ eqv)
              (λ _ → refl)
        )
  ) ( λ i₁ i₂ eqv →
      >>=-resp-⇔≲ eqv
        (λ i → get ⦃ i ⦄) _
        (get-resp-⇔≲ _ _ eqv)
        (λ _ → refl)
  ) 

get-put : □ Equation (State S)
get-put = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄
  where 
    module _ {ε} ⦃ _ : State S ≲ ε ⦄ where
      ctx ret : TypeContext 0 → Set
      ctx _ = ⊤ 
      ret _ = ⊤
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left  _ _ = get >>= put 
      right _ _ = return tt

get-put-respects-⇔≲ : Respects-⇔≲ get-put
get-put-respects-⇔≲ = eq-lawful
  ( λ i₁ i₂ eqv →
      >>=-resp-⇔≲ eqv
        (λ i → get ⦃ i ⦄)
        (λ i → put ⦃ i ⦄)
        (get-resp-⇔≲ _ _ eqv)
        (λ _ → put-resp-⇔≲ _ _ eqv)
  ) (λ i₁ i₂ eqv → refl) 

put-get : □ Equation (State S)
put-get = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄
  where 
    module _ {ε} ⦃ _ : State S ≲ ε ⦄ where
      ctx ret : TypeContext 0 → Set
      ctx _ = S 
      ret _ = S
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left  _ s = put s >> get 
      right _ s = put s >> return s

put-get-respects-⇔≲ : Respects-⇔≲ put-get
put-get-respects-⇔≲ = eq-lawful
  ( λ where
      i₁ i₂ {γ = s} eqv →
        >>=-resp-⇔≲ eqv
          (λ i → put ⦃ i ⦄ s)
          (λ i _ → get ⦃ i ⦄)
          (put-resp-⇔≲ i₁ i₂ eqv)
          (λ _ → get-resp-⇔≲ i₁ i₂ eqv)
  ) ( λ where
    i₁ i₂ {γ = s} eqv →
      >>=-resp-⇔≲ eqv
        (λ i → put ⦃ i ⦄ s)
        (λ i _ → return s)
        (put-resp-⇔≲ i₁ i₂ eqv)
        (λ _ → refl)
  )

put-put : □ Equation (State S) 
put-put = necessary λ {ε} i → left ⦃ i ⦄ ≗ right ⦃ i ⦄ 

  where 
    module _ {ε} ⦃ _ : State S ≲ ε ⦄ where

      ctx ret : TypeContext 0 → Set
      ctx _ = S × S 
      ret _ = ⊤
      left right : Π[ ctx ⇒ ret ⊢ Free ε ]

      left  _ (s , s′) = put s >> put s′ 
      right _ (s , s′) = put s′

put-put-respects-⇔≲ : Respects-⇔≲ put-put
put-put-respects-⇔≲ = eq-lawful
  ( λ where
      i₁ i₂ {γ = s , s′} eqv →
        >>=-resp-⇔≲ eqv
          (λ i → put ⦃ i ⦄ s)
          (λ i _ → put ⦃ i ⦄ s′)
          (put-resp-⇔≲ i₁ i₂ eqv)
          (λ _ → put-resp-⇔≲ i₁ i₂ eqv)
  ) (λ i₁ i₂ eqv → put-resp-⇔≲ i₁ i₂ eqv)


StateTheory : Theory (State S)
StateTheory =
  ∥ get-get
  ∷ get-put
  ∷ put-get 
  ∷ put-put ∷ []
  ∣  get-get-respects-⇔≲
  ∷ get-put-respects-⇔≲
  ∷ put-get-respects-⇔≲
  ∷ put-put-respects-⇔≲
  ∷ []
  ∥ 
  

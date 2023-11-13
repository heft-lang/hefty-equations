module Free.Base where

open import Core.Functor 
open import Core.Container
open import Core.Extensionality

open import Function using (id ; const ; _∘_ ; flip ; _$_)
open import Relation.Unary
open import Data.Product 
open import Data.Sum

open import Relation.Binary.PropositionalEquality

open Container 

data Free (C : Container) : (A : Set) → Set where
  pure   : A → Free C A 
  impure : ∀[ ⟦ C ⟧ᶜ ∘ Free C ⇒ Free C ]

⦅_,_⦆ : (A → B) → Algebraᶜ C B → Free C A → B
⦅_,_⦆ f y (pure x)           = f x
⦅_,_⦆ f y (impure ⟨ s , p ⟩) = y .αᶜ ⟨ s , ⦅ f , y ⦆ ∘ p ⟩

impure′ : Algebraᶜ C (Free C A) 
impure′ = λ where .αᶜ → impure



instance
  free-monad : Monad (Free C)
  free-monad .return = pure
  
  free-monad ._∗ k = ⦅ k , impure′ ⦆
  
identity-fold-lemma : ∀ {c : Free C A} → ⦅ pure , impure′ ⦆ c ≡ c  
identity-fold-lemma {C} {A} {pure _} = refl
identity-fold-lemma {C} {A} {impure ⟨ s , p ⟩} =
  cong (λ □ → impure ⟨ s , □ ⟩) (extensionality λ x → identity-fold-lemma)

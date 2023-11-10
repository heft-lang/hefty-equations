module Core.Functor where

open import Relation.Unary
open import Level renaming (suc to sℓ) 
open import Function

record Functor {a b} (F : Set a → Set b) : Set (sℓ a ⊔ b) where  
  field
    fmap : {A B : Set a} → (A → B) → F A → F B 

open Functor ⦃...⦄ public


record HFunctor {a b} (H : (Set a → Set b) → Set a → Set b) : Set (sℓ (a ⊔ b)) where
  field
    ⦃ HF-functor ⦄ : ∀ {F} → ⦃ Functor F ⦄ → Functor (H F)
    hmap           : ∀ {F G} → ∀[ F ⇒ G ] → ∀[ H F ⇒ H G ]

open HFunctor ⦃...⦄ public 

variable a b : Level
         A : Set a
         B : Set b
         F G : Set a → Set b
         H H₁ H₂ : (Set a → Set b) → Set a → Set b


record Pointed (F : Set → Set) : Set₁ where
  field
    point : ∀[ id ⇒ F ]

open Pointed ⦃...⦄ public

record Monad (F : Set → Set) : Set₁ where
  field
    return : A → F A
    _∗     : (A → F B) → (F A → F B)

  _>>=_ : F A → (A → F B) → F B 
  _>>=_ = flip _∗

  _>>_ : F A → F B → F B
  x >> y = x >>= λ _ → y  

open Monad ⦃...⦄ public 



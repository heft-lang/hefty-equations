module Core.Functor where

open import Relation.Unary
open import Level renaming (suc to sℓ) 
open import Relation.Binary.PropositionalEquality

open import Function

-- Lawful functors on Set, at any level 
record Functor {a b} (F : Set a → Set b) : Set (sℓ a ⊔ b) where  
  field
    fmap : {A B : Set a} → (A → B) → F A → F B

    -- Functor laws 
    fmap-id : ∀ {A : Set a} → ∀ (x : F A) → fmap id x ≡ x
    fmap-∘  :
      ∀ {A B C : Set a}
      → (f : A → B) (g : B → C)
      → (x : F A)
      → fmap g (fmap f x) ≡ fmap (g ∘ f) x 

open Functor ⦃...⦄ public

-- Natural transformations between functors on Set 
record Natural {a b} {F G : Set a → Set b}
               ⦃ _ : Functor F ⦄ ⦃ _ : Functor G ⦄
               (θ : ∀[ F ⇒ G ]) : Set (sℓ a ⊔ b) where
  field
    commute : ∀ {X Y} {f : X → Y} → (x : F X) → θ (fmap f x) ≡ fmap f (θ x) 

open Natural public 

-- Higher-order functors on Set. That is, functors over the category of functors
-- on Set
record HFunctor {a b} (H : (Set a → Set b) → Set a → Set b) : Set (sℓ (a ⊔ b)) where
  field
    -- H should respect functoriality
    ⦃ HF-functor ⦄ : ∀ {F} → ⦃ Functor F ⦄ → Functor (H F)

    -- A "higher-order" map, that associates natural transformations to natural
    -- transformations
    hmap : ∀ {F G} → ∀[ F ⇒ G ] → ∀[ H F ⇒ H G ]

    -- hmap should respect naturality
    hmap-natural :
      ∀ {F G}
      → ⦃ _ : Functor F ⦄ ⦃ _ : Functor G ⦄
      → (θ : ∀[ F ⇒ G ])
      → Natural θ → Natural (hmap θ)

open HFunctor ⦃...⦄ public 

variable a b : Level
         A : Set a
         B : Set b
         F G : Set a → Set b
         H H₁ H₂ : (Set a → Set b) → Set a → Set b

-- Pointed endofunctors on Set 
record Pointed (F : Set → Set) : Set₁ where
  field
    point : ∀[ id ⇒ F ]

open Pointed ⦃...⦄ public

-- Monads on Set 
record Monad (F : Set → Set) : Set₁ where
  field
    return : A → F A
    _∗     : (A → F B) → (F A → F B)

  infixr 5 _>>=_ 
  _>>=_ : F A → (A → F B) → F B 
  _>>=_ = flip _∗

  _>=>_ : {C : Set} → (A → F B) → (B → F C) → A → F C
  (f >=> g) x = f x >>= g 

  _>>_ : F A → F B → F B
  x >> y = x >>= λ _ → y  

open Monad ⦃...⦄ public 



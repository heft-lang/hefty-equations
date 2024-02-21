{-# OPTIONS --without-K #-} 

module Effect.Syntax.Free where

open import Core.Functor
open import Core.Functor.Monad

open import Core.Container
open import Core.Extensionality

open import Function using (id ; const ; _∘_ ; flip ; _$_)
open import Relation.Unary
open import Data.Product 
open import Data.Sum
open import Data.Nat

open import Relation.Unary
open import Relation.Binary.PropositionalEquality

open Container 

data Free (C : Container) (A : Set)  : Set where
  pure   : A → Free C A 
  impure : ⟦ C ⟧ᶜ (Free C A) → Free C A

data Bound {C} : (m : Free C A) → Set₁ where
  leaf : ∀ {x : A} → Bound (pure x)
  node : ∀ (v : ⟦ C ⟧ᶜ (Free C A))
         → ((p : C .position (v .reflectᶜ .proj₁)) → Bound (v .reflectᶜ .proj₂ p))
         → Bound (impure v)



getBound : (m : Free C A) → Bound m 
getBound (pure x) = leaf
getBound (impure ⟨ c , k ⟩) = node ⟨ c , k ⟩ (getBound ∘ k)

fold-free : (A → B) → Algebraᶜ C B → Free C A → B
fold-free f y (pure x)           = f x
fold-free f y (impure ⟨ s , p ⟩) = y .αᶜ ⟨ s , fold-free f y ∘ p ⟩

impure′ : Algebraᶜ C (Free C A) 
impure′ = λ where .αᶜ → impure

map-free : (A → B) → Free C A → Free C B
map-free f = fold-free (pure ∘ f) impure′

map-free-id : (t : Free C A) → map-free id t ≡ t
map-free-id (pure _)           = refl
map-free-id (impure ⟨ s , p ⟩) =
  cong (λ ○ → impure ⟨ s , ○ ⟩)
    (extensionality (map-free-id ∘ p))

map-free-∘ :
  ∀ {D : Set} → (f : A → B) (g : B → D) (t : Free C A)
  → map-free g (map-free f t) ≡ map-free (g ∘ f) t
map-free-∘ f g (pure _)           = refl
map-free-∘ f g (impure ⟨ s , p ⟩) =
  cong (λ ○ → impure ⟨ s , ○ ⟩)
    (extensionality (map-free-∘ f g ∘ p))

hmap-free : C₁ ↦ C₂ → ∀[ Free C₁ ⇒ Free C₂ ]
hmap-free θ = fold-free pure λ where .αᶜ → impure ∘ θ  

instance
  free-functor : Functor (Free C)
  free-functor = record
    { fmap    = map-free
    ; fmap-id = map-free-id
    ; fmap-∘  = map-free-∘
    } 

  free-monad : Monad (Free C)
  free-monad = record
    { return    = pure
    ; _∗        = λ k → fold-free k impure′
    ; >>=-idˡ   = λ _ _ → refl
    ; >>=-idʳ   = right-identity
    ; >>=-assoc = assoc
    }
    where
      right-identity : ∀ (m : Free C A) → flip (λ k → fold-free k impure′) m pure ≡ m
      right-identity (pure _)           = refl
      right-identity (impure ⟨ c , k ⟩) = cong (λ ○ → impure ⟨ c , ○ ⟩) (extensionality $ right-identity ∘ k)

      assoc : {A B D : Set}  (k₁ : A → Free C B) (k₂ : B → Free C D) (m : Free C A)
            → flip (λ k → fold-free k impure′) (flip (λ k → fold-free k impure′) m k₁) k₂
              -------------------------------------------------------------------------------------
            ≡ flip (λ k → fold-free k impure′) m (λ x → flip (λ k → fold-free k impure′) (k₁ x) k₂)
      assoc k₁ k₂ (pure x)           = refl
      assoc k₁ k₂ (impure ⟨ c , k ⟩) = cong (λ ○ → impure ⟨ c , ○ ⟩) (extensionality $ assoc k₁ k₂ ∘ k)

identity-fold-lemma : ∀ {c : Free C A} → fold-free pure impure′ c ≡ c  
identity-fold-lemma {C} {A} {pure _} = refl
identity-fold-lemma {C} {A} {impure ⟨ s , p ⟩} =
  cong (λ ○ → impure ⟨ s , ○ ⟩) (extensionality λ x → identity-fold-lemma)

fmap->>= :
  ∀ {ε} {A B C : Set}
  → (f : B → C) (m : Free ε A)
  → (k : A → Free ε B)
    -----------------------------------
  → fmap f (m >>= k) ≡ m >>= fmap f ∘ k 
fmap->>= f (pure _) _ = refl
fmap->>= f (impure ⟨ c , k′ ⟩) k =
  begin
    fmap f (impure ⟨ c , k′ ⟩ >>= k)
  ≡⟨⟩ 
    fmap f (impure ⟨ c , k′ >=> k ⟩)
  ≡⟨⟩ 
    impure ⟨ c , fmap f ∘ (k′ >=> k) ⟩
  ≡⟨ cong (λ ○ → impure ⟨ c , ○ ⟩) (extensionality λ x → fmap->>= f (k′ x) k) ⟩
    impure ⟨ c , k′ >=> (fmap f ∘ k) ⟩ 
  ≡⟨⟩ 
    impure ⟨ c , k′ ⟩ >>= fmap f ∘ k
  ∎
  where open ≡-Reasoning

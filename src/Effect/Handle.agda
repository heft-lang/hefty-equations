{-# OPTIONS --without-K #-} 

open import Relation.Unary

open import Core.Functor
open import Core.Functor.NaturalTransformation
open import Core.Functor.Monad

open import Core.Container
open import Core.Signature
open import Core.Extensionality

open import Effect.Base
open import Effect.Syntax.Free

open import Data.Empty 
open import Data.Product
open import Data.Sum

open import Effect.Separation
open import Effect.Inclusion

open import Function hiding (_⇔_)

open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_]) hiding (naturality)

module Effect.Handle where


{- Semantics for 1st order effects -}


fwd : {P : Set} → Algebraᶜ C (P → Free C A)
fwd .αᶜ ⟨ c , p ⟩ v = impure ⟨ c , flip p v ⟩
       
separate : ε₁ ∙ ε₂ ≈ ε′ → ∀[ Free ε′ ⇒ Free (ε₁ ⊕ᶜ ε₂) ]
separate σ = hmap-free (Union.proj σ)

-- Handers of an effect are algebras over its signatures
record Handler (ε : Effect) (P : Set) (F : Set → Set) : Set₁ where
  field
    gen   : ∀[ id ⇒ const P ⇒ F ] 
    hdl   : ∀ {ε′} → Algebraᶜ ε (P → Free ε′ (F A)) 

  handle′ : ∀[ Free (ε ⊕ᶜ ε₂) ⇒ const P ⇒ F ⊢ Free ε₂ ]
  handle′ m x = fold-free (pure ∘₂ gen) (hdl ⟨⊕⟩ᶜ fwd) m x 

  handle : ε ∙ ε₂ ≈ ε′ → ∀[ Free ε′ ⇒ const P ⇒ F ⊢ Free ε₂ ] 
  handle σ m x = handle′ (separate σ m) x

  ℋ⟦_⟧ : ⦃ ε ≲ ε′ ⦄ → ∀[ Free ε′ ⇒ const P ⇒ F ⊢ Free ε′ ]
  ℋ⟦_⟧ ⦃ i ⦄ m p = ♯ ⦃ _ , union-comm (i .proj₂) ⦄ (handle (i .proj₂) m p) 

open Handler 
open Inverse
open Union


Modular′′ : (H : Handler ε₁ A F) → Set₁
Modular′′ {ε₁} H =
  ∀ {B ε₂} (c : ε₂ .shape)
  → (k : (ε₁ ⊕ᶜ ε₂) .position (inj₂ c) → Free (ε₁ ⊕ᶜ ε₂) B)
  → (x : _) 
  → handle′ H {ε₂ = ε₂} (impure ⟨ inj₂ c , k ⟩) x ≡ impure ⟨ c , flip (handle′ H) x ∘ k ⟩ 

Modular′ : (H : Handler ε₁ A F) → Set₁
Modular′ {ε₁ = ε₁} H =
  ∀ {B ε₂} (m : Free ε₂ B)
  → (x : _)
    ------------------------------------------------
  → handle′ H (♯ʳ ε₁ m) x ≡ fmap (flip (H .gen) x) m 

-- Defines "modular handlers", that asserts that a handler leaves alone nodes in
-- the tree containing commands of other effects than the effect it handles. 
Modular : (H : Handler ε₁ A F) → Set₁
Modular {ε₁ = ε₁} H =
  ∀ {B ε₂ ε} (m : Free ε₂ B)
  → (σ : ε₁ ∙ ε₂ ≈ ε)
  → (x : _)
    -------------------------------------------------------------
  → handle H {ε₂ = ε₂} σ (♯ʳ′ σ m) x ≡ fmap (flip (H .gen) x) m


Coherent′ : {P : Set} → ⦃ ∀ {ε} → Monad (const P ⇒ F ⊢ Free ε) ⦄ → (H : Handler ε₁ P F) → Set₁
Coherent′ {ε₁ = ε₁} ⦃ p ⦄ H =
  ∀ {B C ε₂}
  → (m : Free (ε₁ ⊕ᶜ ε₂) B) (k : B → Free (ε₁ ⊕ᶜ ε₂) C)
    --------------------------------------------------------------
  → handle′ H {ε₂ = ε₂} (m >>= k) ≡ (handle′ H m) >>= (handle′ H ∘ k)


Coherent : {P : Set}  → ⦃ ∀ {ε} → Monad (const P ⇒ F ⊢ Free ε) ⦄ → (H : Handler ε₁ P F) → Set₁
Coherent {ε₁ = ε₁} H =
  ∀ {B C ε₂ ε}
  → (σ : ε₁ ∙ ε₂ ≈ ε)
  → (m : Free ε B) (k : B → Free ε C)
    ------------------------------------------------------
  → handle H σ (m >>= k) ≡ handle H σ m >>= handle H σ ∘ k


open ≡-Reasoning 

weaken-lemma : (σ : ε₁ ∙ ε₂ ≈ ε) → (m : Free ε₂ A) → separate σ (♯ʳ′ σ m) ≡ ♯ʳ ε₁ m
weaken-lemma               σ (pure _)           = refl
weaken-lemma {ε₁} {ε₂} {ε} σ (impure ⟨ c , r ⟩) =
  begin
    separate σ (♯ʳ′ σ (impure ⟨ c , r ⟩))
  ≡⟨⟩ 
    hmap-free (proj σ) (impure (injb σ ⟨ c , ♯ʳ′ σ ∘ r ⟩) )
  ≡⟨⟩ 
    impure (proj σ (fmap (separate σ) (injb σ ⟨ c , ♯ʳ′ σ ∘ r ⟩))) 
  ≡⟨ cong (impure ∘ proj σ) (sym $ injb-natural σ .commute {f = fmap (separate σ)} ⟨ c , ♯ʳ′ σ ∘ r ⟩)  ⟩
    impure (proj σ (injb σ (fmap (separate σ) ⟨ c , ♯ʳ′ σ ∘ r ⟩))) 
  ≡⟨ cong impure (σ .union .equivalence _ .inverse .proj₂ _) ⟩ 
    impure ⟨ inj₂ c , (separate σ ∘ ♯ʳ′ σ) ∘ r ⟩ 
  ≡⟨ cong (λ ○ → impure ⟨ inj₂ c , ○ ⟩) (extensionality $ weaken-lemma σ ∘ r) ⟩
    impure ⟨ inj₂ c , ♯ʳ ε₁ ∘ r ⟩ 
  ≡⟨⟩ {- Definition of ♯ʳ -}  
    ♯ʳ ε₁ (impure ⟨ c , r ⟩)
  ∎

sep-modular : (H : Handler ε₁ A F) → Modular′ H → Modular H
sep-modular {ε₁} H mod m σ p =
  begin
    handle′ H (separate σ (♯ʳ′ σ m)) p
  ≡⟨ cong (λ ○ → handle′ H ○ p) (weaken-lemma σ m) ⟩
    handle′ H (♯ʳ ε₁ m) p 
  ≡⟨ mod m p ⟩ 
    fmap (flip (H .gen) p) m
  ∎

separate-coherent :
  ∀ (m : Free ε A) (k : A → Free ε B)
  → (σ : ε₁ ∙ ε₂ ≈ ε)
  → separate σ (m >>= k) ≡ separate σ m >>= separate σ ∘ k
separate-coherent (pure x)           k σ = refl
separate-coherent {ε₁ = ε₁} {ε₂ = ε₂} (impure ⟨ c , r ⟩) k σ = 
  begin
    separate σ (impure ⟨ c , r ⟩ >>= k)
  ≡⟨⟩ 
    impure (Union.proj σ ⟨ (c , separate σ ∘ (r >=> k)) ⟩)
  ≡⟨ cong (λ ○ → impure (Union.proj σ ⟨ c , ○ ⟩)) (extensionality λ y → separate-coherent (r y) k σ) ⟩ 
    impure (proj σ ⟨ c , ((separate σ ∘ r) >=> (separate σ ∘ k)) ⟩)
  ≡⟨ cong impure (proj-natural σ .commute {f = _>>= separate σ ∘ k} ⟨ c , separate σ ∘ r ⟩) ⟩ 
    impure (fmap {F = ⟦ ε₁ ⊕ᶜ ε₂ ⟧ᶜ} (_>>= separate σ ∘ k) (Union.proj σ ⟨ c , separate σ ∘ r ⟩)) 
  ≡⟨⟩
    impure (Union.proj σ ⟨ c , separate σ ∘ r ⟩) >>= separate σ ∘ k
  ≡⟨⟩ 
    separate σ (impure ⟨ c , r ⟩) >>= separate σ ∘ k
  ∎

sep-coherent : ⦃ _ : ∀ {ε} → Monad (const A ⇒ F ⊢ Free ε) ⦄ → (H : Handler ε₁ A F) → Coherent′ H → Coherent H
sep-coherent H C σ m k = 
  begin
    handle H σ (m >>= k)
  ≡⟨⟩ 
    handle′ H (separate σ (m >>= k))
  ≡⟨ cong (handle′ H) (separate-coherent m k σ) ⟩ 
    handle′ H (separate σ m >>= separate σ ∘ k)
  ≡⟨ C (separate σ m) (separate σ ∘ k) ⟩ 
    handle H σ m >>= handle H σ ∘ k
  ∎

handle-modular′′ : (H : Handler ε A F) → Modular′′ H
handle-modular′′ H c k x = refl

-- Proves the "stricter" notion of modularity for handlers, i.e., if the effect
-- to be handled is already at the front
handle-modular′ : (H : Handler ε A F) → Modular′ H
handle-modular′     H (pure x)           a = refl
handle-modular′ {ε} H (impure ⟨ c , r ⟩) a = begin
    impure ⟨ c , (flip (handle′ H) a ∘ ♯ʳ ε) ∘ r ⟩
  ≡⟨ cong (λ ○ → impure ⟨ c , ○ ⟩) (extensionality λ p → handle-modular′ H (r p) a) ⟩
    impure ⟨ c , fmap (flip (H .gen) a) ∘ r ⟩
  ∎

handle-modular : (H : Handler ε A F) → Modular H
handle-modular H = sep-modular H (handle-modular′ H)



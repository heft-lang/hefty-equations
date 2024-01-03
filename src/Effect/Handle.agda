open import Relation.Unary

open import Core.Functor
open import Core.Container
open import Core.Signature
open import Core.DisjointUnion
open import Core.Extensionality

open import Free.Base
open import Hefty.Base
open import Effect.Base

open import Data.Empty 
open import Data.Product
open import Data.Sum

open import Effect.Separation

open import Function hiding (_⇔_)

open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])

module Effect.Handle where


{- Semantics for 1st order effects -}


-- Handers of an effect are algebras over its signatures
record Handler (ε : Effect) (P : Set) (F : Set → Set) : Set₁ where
  field
    gen   : ∀[ id ⇒ const P ⇒ F ] 
    hdl   : ∀ {ε′} → Algebraᶜ ε (P → Free ε′ (F A))      

open Handler public 

fwd : {P : Set} → Algebraᶜ C (P → Free C A)
fwd .αᶜ ⟨ c , p ⟩ v = impure ⟨ c , flip p v ⟩

open Inverse
open DisjointUnion
open _∙_≈_

separate : ε₁ ∙ ε₂ ≈ ε → ∀[ Free ε ⇒ Free (ε₁ ⊕ᶜ ε₂) ]
separate σ = hmap-free (coproduct-lemma .to ∘ σ .sep _ .union .from)

handle′ : Handler ε₁ A F → A → ∀[ Free (ε₁ ⊕ᶜ ε₂) ⇒ F ⊢ Free ε₂ ]
handle′ H x m = fold-free (pure ∘₂ H .gen) (H .hdl ⟨⊕⟩ᶜ fwd) m x 

handle : Handler ε₁ A F → ε₁ ∙ ε₂ ≈ ε → A → ∀[ Free ε ⇒ F ⊢ Free ε₂ ] 
handle H σ x m = handle′ H x (separate σ m)

Modular′ : (H : Handler ε₁ A F) → Set₁
Modular′ {ε₁ = ε₁} H =
  ∀ {B ε₂} (m : Free ε₂ B)
  → (x : _)
    ------------------------------------------------
  → handle′ H x (♯ʳ ε₁ m) ≡ fmap (flip (H .gen) x) m 


-- Defines "modular handlers", that asserts that a handler leaves alone nodes in
-- the tree containing commands of other effects than the effect it handles. 
Modular : (H : Handler ε₁ A F) → Set₁
Modular {ε₁ = ε₁} H =
  ∀ {B ε₂ ε} (m : Free ε₂ B)
  → (σ : ε₁ ∙ ε₂ ≈ ε)
  → (x : _)
    -------------------------------------------------
  → handle′ H x (separate σ (♯ʳ′ σ m)) ≡ fmap (flip (H .gen) x) m
 

open ≡-Reasoning 

weaken-lemma : (σ : ε₁ ∙ ε₂ ≈ ε) → (m : Free ε₂ A) → separate σ (♯ʳ′ σ m) ≡ ♯ʳ ε₁ m
weaken-lemma      σ (pure _)           = refl
weaken-lemma {ε₁} {ε₂} σ (impure ⟨ c , r ⟩) = begin
    separate σ (♯ʳ′ σ (impure ⟨ c , r ⟩))
  ≡⟨⟩ {- Definition of ♯ʳ′ -} 
    separate σ (inject ⦃ ≲-∙-right σ ⦄ .αᶜ ⟨ c , ♯ʳ′ σ ∘ r ⟩)
  ≡⟨⟩ {- definition of inject -} 
    separate σ (impure (σ .sep _ .union .to (inj₂ ⟨ c , ♯ʳ′ σ ∘ r ⟩)))
  ≡⟨⟩ {- Definition of separate -} 
    hmap-free
      (coproduct-lemma .to ∘ σ .sep _ .union .from)
      (impure (σ .sep _ .union .to (inj₂ ⟨ c , ♯ʳ′ σ ∘ r ⟩)))
  ≡⟨⟩ {- Definition of hmap -} 
    fold-free pure
      (λ where .αᶜ → impure ∘ (coproduct-lemma .to ∘ σ .sep _ .union .from))
      (impure (σ .sep _ .union .to (inj₂ ⟨ c , ♯ʳ′ σ ∘ r ⟩)))
  ≡⟨⟩ {- Definition of fold-free -} 
    impure (coproduct-lemma .to
      ( σ .sep _ .union .from (fmap (separate σ)
        ( (σ .sep _ .union .to (inj₂ ⟨ c , ♯ʳ′ σ ∘ r ⟩))
        )))) 
  ≡⟨ cong (λ ○ → impure (coproduct-lemma .to (σ .sep _ .union .from ○))) (lemma (separate σ) ⟨ c , ♯ʳ′ σ ∘ r ⟩ ) ⟩
    impure (coproduct-lemma .to
      ( σ .sep _ .union .from (σ .sep _ .union .to
        ( inj₂ ⟨ c , separate σ ∘ ♯ʳ′ σ ∘ r ⟩)
        ))) 
  ≡⟨ cong (λ ○ → impure (coproduct-lemma .to ○)) (σ .sep _ .union .inverse .proj₂ _) ⟩
    impure (coproduct-lemma {ε₁} {ε₂} .to (inj₂ ⟨ c , separate σ ∘ ♯ʳ′ σ ∘ r ⟩))  
  ≡⟨⟩ 
    impure ⟨ inj₂ c , (separate σ ∘ ♯ʳ′ σ) ∘ r ⟩ 
  ≡⟨ cong (λ ○ → impure ⟨ inj₂ c , ○ ⟩) (extensionality $ weaken-lemma σ ∘ r) ⟩
    impure ⟨ inj₂ c , ♯ʳ ε₁ ∘ r ⟩ 
  ≡⟨⟩ {- Definition of ♯ʳ -} 
    ♯ʳ ε₁ (impure ⟨ c , r ⟩) 
  ∎
  where
    -- TODO: this looks like a naturality square. Most likely we should amend
    -- the definition of effect separation to require that the isomorphism that
    -- witnesses it is in fact a natural iso. Same for effect inclusion. 
    postulate lemma : ∀ f v → fmap f ((σ .sep _ .union .to (inj₂ v))) ≡ σ .sep _ .union .to (inj₂ (fmap f v))


sep-modular : (H : Handler ε₁ A F) → Modular′ H → Modular H
sep-modular {ε₁} H mod m σ a = begin
    handle′ H a (separate σ (♯ʳ′ σ m))
  ≡⟨ cong (λ ○ → handle′ H a ○) (weaken-lemma σ m) ⟩
    handle′ H a (♯ʳ ε₁ m) 
  ≡⟨ mod m a ⟩ 
    fmap (flip (H .gen) a) m
  ∎ 

-- Proves the "stricter" notion of modularity for handlers, i.e., if the effect
-- to be handled is already at the front
handle-modular′ : (H : Handler ε A F) → Modular′ H
handle-modular′     H (pure x)           a = refl
handle-modular′ {ε} H (impure ⟨ c , r ⟩) a = begin
    impure ⟨ c , (handle′ H a ∘ ♯ʳ ε) ∘ r ⟩
  ≡⟨ cong (λ ○ → impure ⟨ c , ○ ⟩) (extensionality λ p → handle-modular′ H (r p) a) ⟩
    impure ⟨ c , fmap (flip (H .gen) a) ∘ r ⟩
  ∎

open import Relation.Unary

open import Core.Functor
open import Core.Container
open import Core.Signature

open import Free.Base
open import Hefty.Base

open import Data.Empty 
open import Data.Product
open import Data.Sum

open import Function

open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality using (refl ; _≡_ ; subst ; sym ; trans)

module Effect.Base where

Effect  = Container 
Effectᴴ = Signature

↑ : Effect → Effectᴴ
↑ ε = record
  { command  = ε .shape
  ; response = ε .position
  ; fork     = λ _ → ⊥ 
  ; returns  = λ()
  }

variable ε ε₁ ε₂ ε₃ ε′ : Effect
         η η₁ η₂ η₃ η′ : Effectᴴ 

embed : ∀[ F ⊢ ⟦ ε ⟧ᶜ ⇒ ⟦ ↑ ε ⟧ F ]
embed ⟨ s , p ⟩ .reflect = s , p , λ()

embed-free : ∀[ Free ε ⇒ Hefty (↑ ε) ]
embed-free = ⦅ pure , (λ where .αᶜ x → impure (embed x)) ⦆


-- Container/effect morphisms

record _⊑_ (ε₁ ε₂ : Effect) : Set₁ where
  field inj : ∀[ ⟦ ε₁ ⟧ᶜ ⇒ ⟦ ε₂ ⟧ᶜ ]



open _⊑_ ⦃...⦄ public

inject : ⦃ ε₁ ⊑ ε₂ ⦄ → Algebraᶜ ε₁ (Free ε₂ A) 
inject .αᶜ = impure ∘ inj 

-- Effect weakening / masking for the free monad
--
-- Viewing containers as a category (with injections as morphisms), this defines
-- the action on morphisms of the Functor Free ∈ [Container,[Set,Set]]
♯_ : ⦃ ε₁ ⊑ ε₂ ⦄ → ∀[ Free ε₁ ⇒ Free ε₂ ]
♯_ = ⦅ pure , inject ⦆

-- Container morphisms are reflexive and transitive (i.e., they compose & have identities)
--
-- For `Free` to be a proper functor, weakening should respect these 

instance ⊑-refl : ε ⊑ ε
⊑-refl .inj = id

⊑-trans : ε₁ ⊑ ε₂ → ε₂ ⊑ ε₃ → ε₁ ⊑ ε₃
⊑-trans sub₁ sub₂ .inj = sub₂ .inj ∘ sub₁ .inj

⊑-⊕ᶜ-left : ∀ ε′ → ε ⊑ (ε ⊕ᶜ ε′)
⊑-⊕ᶜ-left _ .inj ⟨ s , p ⟩ = ⟨ inj₁ s , p ⟩ 

⊑-⊕ᶜ-right : ∀ ε′ → ε ⊑ (ε′ ⊕ᶜ ε)
⊑-⊕ᶜ-right _ .inj ⟨ s , p ⟩ = ⟨ inj₂ s , p ⟩

{- Semantics for 1st order effects -}

record Handler (C : Container) (P : Set) (F : Set → Set) (A : Set) : Set₁ where
  field
    gen   : A → P → (F A) 
    hdl   : ∀ {C′} → Algebraᶜ C (P → Free C′ (F A))      

open Handler public 

fwd : {P : Set} → Algebraᶜ C (P → Free C A)
fwd .αᶜ ⟨ c , p ⟩ v = impure ⟨ c , flip p v ⟩ 

handle : {P : Set} → ∀[ Handler C₁ P F ⇒  Free (C₁ ⊕ᶜ C₂) ⇒ const P ⇒ F ⊢ Free C₂ ]
handle h = ⦅ (λ x v → return (h .gen x v)) , (h .hdl ⟨⊕⟩ᶜ fwd) ⦆



-- Signature/highe-order effect morphisms

record _⊑ᴴ_ (η₁ η₂ : Effectᴴ) : Set₁ where
  field
  
    injᴴ-c          : η₁ .command → η₂ .command
    
    response-stable : ∀ {c}
                      → η₁ .response c ≡ η₂ .response (injᴴ-c c)
                      
    fork-stable     : ∀ {c}
                      → η₁ .fork c ≡ η₂ .fork (injᴴ-c c)
                      
    types-stable    : ∀ {c} {ψ : η₂ .fork (injᴴ-c c)}
                      → η₁ .returns (subst id (sym fork-stable) ψ) ≡ η₂ .returns ψ

  injᴴ : ⦃ Functor F ⦄ → ∀[ ⟦ η₁ ⟧ F ⇒ ⟦ η₂ ⟧ F ]
  injᴴ ⟪ c , r , s ⟫ =
    ⟪ (injᴴ-c c
    , r ∘ subst id (sym response-stable)
    , fmap (subst id types-stable) ∘ s ∘ subst id (sym fork-stable))
    ⟫

postulate injᴴ-command : ⦃ η₁ ⊑ᴴ η₂ ⦄ → η₁ .command → η₂ .command

open _⊑ᴴ_ ⦃...⦄ public 

injectᴴ : ⦃ η₁ ⊑ᴴ η₂ ⦄ → Algebra η₁ (Hefty η₂)
injectᴴ .α v = impure (injᴴ v)  


♯ᴴ : ⦃ η₁ ⊑ᴴ η₂ ⦄ → ∀[ Hefty η₁ ⇒ Hefty η₂ ]
♯ᴴ = fold-hefty {F = Hefty _} pure injectᴴ

⊑ᴴ-refl : η ⊑ᴴ η
⊑ᴴ-refl = record
  { injᴴ-c          = id
  ; response-stable = refl
  ; fork-stable     = refl
  ; types-stable    = refl
  }  

postulate TODO : ∀ {a} {A : Set a} → A 

⊑ᴴ-trans : η₁ ⊑ᴴ η₂ → η₂ ⊑ᴴ η₃ → η₁ ⊑ᴴ η₃
⊑ᴴ-trans sub₁ sub₂ = record
  { injᴴ-c          = injᴴ-c ⦃ sub₂ ⦄ ∘ injᴴ-c ⦃ sub₁ ⦄
  ; response-stable = trans (response-stable ⦃ sub₁ ⦄) (response-stable ⦃ sub₂ ⦄)
  ; fork-stable     = trans (fork-stable ⦃ sub₁ ⦄) (fork-stable ⦃ sub₂ ⦄)
  ; types-stable    = trans TODO (types-stable ⦃ sub₂ ⦄)
  }



⊑ᴴ-⊕-left : η₁ ⊑ᴴ (η₁ ⊕ η₂)
⊑ᴴ-⊕-left = record
  { injᴴ-c          = inj₁
  ; response-stable = refl
  ; fork-stable     = refl
  ; types-stable    = refl
  } 

⊑ᴴ-⊕-right : η₂ ⊑ᴴ (η₁ ⊕ η₂)
⊑ᴴ-⊕-right = record
  { injᴴ-c          = inj₂
  ; response-stable = refl
  ; fork-stable     = refl
  ; types-stable    = refl
  }



{- Semantics for higher-order effects -}

record Elaboration (η : Effectᴴ) (ε : Effect) : Set₁ where
  field
    elab : Algebra η (Free ε) 

  elaborate : ∀[ Hefty η ⇒ Free ε ]
  elaborate = fold-hefty pure elab 

open Elaboration public 

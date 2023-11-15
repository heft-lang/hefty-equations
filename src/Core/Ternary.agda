open import Data.Product 

open import Relation.Unary
open import Relation.Binary hiding (_⇔_)
open import Function hiding (_⇔_)

open import Level

module Core.Ternary {c} (Carrier : Set c) where


-- Biimplication for predicates 
_⇔_ : ∀ {a b} {A : Set a} → (P Q : Pred A b) → Pred A b
(P ⇔ Q) x = P x ↔ Q x

Rel₃ : (ℓ : Level) → Set (suc ℓ ⊔ c)
Rel₃ ℓ = (c₁ c₂ c : Carrier) → Set ℓ


module _ {ℓ} (_∙_≈_ : Rel₃ ℓ) where 

  _∙_ : (c₁ c₂ : Carrier) → Pred Carrier ℓ
  c₁ ∙ c₂ = c₁ ∙ c₂ ≈_

  LeftIdentity : (e : Carrier) → Set (ℓ ⊔ c)
  LeftIdentity e =
    ∀ {c} → e ∙ c ≈ c 

  RightIdentity : (e : Carrier) → Set (ℓ ⊔ c)
  RightIdentity e =
    ∀ {c} → c ∙ e ≈ c

  Commutative : Set (ℓ ⊔ c)
  Commutative =
    ∀ {c₁ c₂ c} → c₁ ∙ c₂ ≈ c → c₂ ∙ c₁ ≈ c

  RightAssociative : Set (ℓ ⊔ c)
  RightAssociative =
    ∀ {a b ab c abc}
      → a ∙ b ≈ ab → ab ∙ c ≈ abc
      → ∃ λ bc → a ∙ bc ≈ abc × b ∙ c ≈ bc
  
  LeftAssociative : Set (ℓ ⊔ c)
  LeftAssociative =
    ∀ {a bc b c abc}
    → a ∙ bc ≈ abc → b ∙ c ≈ bc →
    ∃ λ ab → ab ∙ c ≈ abc × a ∙ b ≈ ab

  record Functional {r} (_≈_ : Rel Carrier r) : Set (ℓ ⊔ c ⊔ r) where
    field
      f1 : ∀ {c₁ c₁′ c₂ c} → c₁ ∙ c₂ ≈ c → c₁′ ∙ c₂  ≈ c  → c₁ ≈ c₁′  
      f2 : ∀ {c₁ c₂ c₂′ c} → c₁ ∙ c₂ ≈ c → c₁  ∙ c₂′ ≈ c  → c₂ ≈ c₂′  
      f3 : ∀ {c₁ c₂ c c′ } → c₁ ∙ c₂ ≈ c → c₁  ∙ c₂  ≈ c′ → c  ≈ c′   

  open Functional public

  record Respects {r} (_≈_ : Rel Carrier r) : Set (ℓ ⊔ c ⊔ r) where
    field
      r1 : ∀ {c₁ c₁′ c₂ c} → c₁ ≈ c₁′ → c₁ ∙ c₂ ≈ c → c₁′ ∙ c₂  ≈ c
      r2 : ∀ {c₁ c₂ c₂′ c} → c₂ ≈ c₂′ → c₁ ∙ c₂ ≈ c → c₁  ∙ c₂′ ≈ c
      r3 : ∀ {c₁ c₂ c c′}  → c  ≈ c′  → c₁ ∙ c₂ ≈ c → c₁  ∙ c₂  ≈ c′ 

  Ext : Rel Carrier _
  Ext c₁ c = ∃ λ c₂ → c₁ ∙ c₂ ≈ c

  Ext-reflexive : ∃⟨ RightIdentity ⟩ → Reflexive Ext
  Ext-reflexive (_ , σ) = _ , σ 

  Ext-transitive : RightAssociative → Transitive Ext
  Ext-transitive assoc (i′ , σ₁) (j′ , σ₂) with assoc σ₁ σ₂
  ... | ij′ , σ₃ , σ₄ = ij′ , σ₃

import Relation.Unary 

open import Core.Ternary as Ternary

open import Function hiding (_⟨_⟩_)
open import Level
open import Data.Product

open import Relation.Binary.Bundles
import Relation.Binary.PropositionalEquality as ≡

module Core.Logic {ℓ} (Carrier : Set ℓ) (_∙_≈_ : Rel₃ ℓ ℓ Carrier ) where

open Relation.Unary  public   
open Ternary.Relation Carrier _∙_≈_

variable P Q P₁ P₂ Q₁ Q₂ P′ Q′ : Pred Carrier ℓ


record Monotone (P : Pred Carrier ℓ) : Set (suc ℓ) where
  field weaken : ∀ {x y} → Ext x y → P x → P y 

open Monotone ⦃...⦄ public 

record Antitone (P : Pred Carrier ℓ) : Set (suc ℓ) where 
  field strengthen : ∀ {x y} → Ext x y → P y → P x

open Antitone ⦃...⦄ public 

record RespectsMonotonicity (T : Pred Carrier ℓ → Pred Carrier ℓ) : Set (suc ℓ) where
  field
    respects-monotonicity : ∀ {P} → Monotone P → Monotone (T P)

open RespectsMonotonicity public

transform-monotone : ∀ {T} → ⦃ RespectsMonotonicity T ⦄ → ⦃ m : Monotone P ⦄ → Monotone (T P)
transform-monotone ⦃ rm ⦄ ⦃ m ⦄ = record { weaken = weaken ⦃ rm .respects-monotonicity m ⦄ }  

record _⊣_ (L R : Pred Carrier ℓ → Pred Carrier ℓ) ⦃ lrm : RespectsMonotonicity L ⦄ ⦃ rrm : RespectsMonotonicity R ⦄ : Set (suc ℓ) where 
  field
    iso : ⦃ Monotone P ⦄ → ⦃ Monotone Q ⦄ → ∀[ L P ⇒ Q ] ↔ ∀[ P ⇒ R Q ]


  module _ {P Q} ⦃ pm : Monotone P ⦄ ⦃ qm : Monotone Q ⦄ where 
    open Inverse (iso {P} {Q} ⦃ pm ⦄ ⦃ qm ⦄) 

    φ = from
    φᵒ = to

  -- Every pair of adjoint predicate transformers gives rise to a monad/comonad pair

  M : Pred Carrier ℓ → Pred Carrier ℓ
  M = R ∘ L

  W : Pred Carrier ℓ → Pred Carrier ℓ
  W = L ∘ R

  unit : ⦃ Monotone P ⦄ → ∀[ P ⇒ M P ]
  unit ⦃ m ⦄ = φᵒ ⦃ m ⦄ ⦃ transform-monotone ⦃ m = m ⦄ ⦄ id

  counit : ⦃ Monotone P ⦄ → ∀[ W P ⇒ P ]
  counit ⦃ m ⦄ = φ ⦃ transform-monotone ⦃ m = m ⦄ ⦄ ⦃ m ⦄ id

-- TODO : this requires additionaly that P and Q are functorial/monotone, and
-- that L and R respect this structure
-- 
--   join : ∀[ M (M P) ⇒ M P ]
--   join = {!!}
-- 
--   duplicate : ∀[ W P ⇒ W (W P) ]
--   duplicate = {!!} 

open _⊣_ 



{- Stars and magic -} 

record _✴_ (P Q : Pred Carrier ℓ) (x : Carrier) : Set ℓ where 
  constructor _✴⟨_⟩_
  field
    {c₁ c₂} : Carrier
    px  : P c₁
    sep : c₁ ∙ c₂ ≈ x
    qx  : Q c₂

record _─✴_ (P Q : Pred Carrier ℓ) (x : Carrier) : Set ℓ where
  constructor wand
  field
    _⟨_⟩_ : ∀ {c₁ c₂} → x ∙ c₁ ≈ c₂ → P c₁ → Q c₂

open _✴_
open _─✴_


-- We might view this as defining the "internal currying adjunction" in the
-- category of monotone predicates
module _ (assocʳ : RightAssociative) (assocˡ : LeftAssociative) where

  ✴-curry : ∀[ (P₁ ✴ P₂) ─✴ Q ⇒ P₁ ─✴ (P₂ ─✴ Q) ]
  ✴-curry f = wand
    λ σ₁ px₁ → wand
      λ σ₂ px₂ →
        f ⟨ assocʳ σ₁ σ₂ .proj₂ .proj₁
          ⟩ ( px₁ ✴⟨ assocʳ σ₁ σ₂ .proj₂ .proj₂
                   ⟩ px₂) 

  ✴-uncurry : ∀[ P₁ ─✴ (P₂ ─✴ Q) ⇒ (P₁ ✴ P₂) ─✴ Q ]
  ✴-uncurry f = wand
    λ σ ppx →
      ( f ⟨ assocˡ σ (ppx .sep) .proj₂ .proj₂
          ⟩ ppx .px
      ) ⟨ assocˡ σ (ppx .sep) .proj₂ .proj₁
        ⟩ ppx .qx


-- But, to show that ✴ and ─✴ are adjoint (and thus that the category of
-- monotone predicates is closed monoidal), we require a bijection of homsets,
-- which means we define curry/uncurry as natural transformations. 

✴-curry′ : ∀[ (P₁ ✴ P₂) ⇒ Q ] → ∀[ P₁ ⇒ (P₂ ─✴ Q) ]
✴-curry′ f px₁ = wand (λ σ px₂ → f (px₁ ✴⟨ σ ⟩ px₂))
                                               
✴-uncurry′ : ∀[ P₁ ⇒ (P₂ ─✴ Q) ] → ∀[ (P₁ ✴ P₂) ⇒ Q ]
✴-uncurry′ f (px₁ ✴⟨ σ ⟩ px₂) = f px₁ ⟨ σ ⟩ px₂
-- 
-- ✴-adjoint : ∀ P → (_✴ P) ⊣ (P ─✴_)
-- ✴-adjoint P .iso = record
--   { to        = ✴-curry′
--   ; from      = ✴-uncurry′
--   ; to-cong   = λ where ≡.refl → ≡.refl
--   ; from-cong = λ where ≡.refl → ≡.refl
--   ; inverse   = (λ x → ≡.refl) , λ x → ≡.refl
--   } 
-- 
-- A "separating state monad". It is defined as `S ─✴ (P ✴ S)`, but we get it's
-- monadic structure for free if we define it by going through adjunction that
-- witnesses the closed monoidal structure of the category of monotone predictes
-- in terms of ✴/─✴
-- State✴ : Pred Carrier ℓ → Pred Carrier ℓ → Pred Carrier ℓ
-- State✴ = M ∘ ✴-adjoint 




{- Boxes and diamonds -} 


-- The posibility modality. One way to think about posibility is as a unary
-- version of separating conjunction. 
record ◇ (P : Pred Carrier ℓ) (x : Carrier) : Set ℓ where
  constructor ◇⟨_⟩_ 
  field
    {x′}    : Carrier
    i       : Ext x′ x 
    px      : P x′

open ◇

-- The necessity modality. In a similar spirit, we can view necessity as a unary
-- version of separating implication.
record □ (P : Pred Carrier ℓ) (x : Carrier) : Set ℓ where
  constructor necessary 
  field
    □⟨_⟩_ : ∀ {x′} → Ext x x′ → P x′  

open □

mod-curry : ∀[ ◇ P ⇒ Q ] → ∀[ P ⇒ □ Q ]
mod-curry f px = necessary λ i → f $ ◇⟨ i ⟩ px 

mod-uncurry : ∀[ P ⇒ □ Q ] → ∀[ ◇ P ⇒ Q ]
mod-uncurry f (◇⟨ i ⟩ px) = □⟨ f px ⟩ i

-- 
-- mod-adjoint : ◇ ⊣ □
-- mod-adjoint .iso = record
--   { to        = mod-curry
--   ; from      = mod-uncurry
--   ; to-cong   = λ where ≡.refl → ≡.refl
--   ; from-cong = λ where ≡.refl → ≡.refl
--   ; inverse   = (λ _ → ≡.refl) , λ _ → ≡.refl
--   }
--   

{- A "Kripke closed monoidal structure" on the category of monotone predicates -} 

-- The "Kripke exponent" (or, Kripke function space) between two predicates is
-- defined as the necessity of their implication.
_⇛_ : (P Q : Pred Carrier ℓ) → Pred Carrier ℓ
P ⇛ Q = □ (P ⇒ Q)


-- Since the Kripke tensor has a right adjoint, it defines *another* closed
-- monoidal structure on the category of monotone predicates, with Kripke
-- function spaces as the exponential objects

module _ (∙-unitʳ : ∃⟨ RightIdentity ⟩) (∙-assocʳ : RightAssociative) where

  open Preorder (Ext-preorder ∙-unitʳ ∙-assocʳ)

  kripke-curry : ⦃ _ : Monotone P₁ ⦄ → ∀[ (P₁ ∩ P₂) ⇒ Q ] → ∀[ P₁ ⇒ (P₂ ⇛ Q) ] 
  kripke-curry f px₁ = necessary λ i px₂ → f (weaken i px₁ , px₂) 

  kripke-uncurry : ∀[ P₁ ⇒ (P₂ ⇛ Q) ] → ∀[ (P₁ ∩ P₂) ⇒ Q ] 
  kripke-uncurry f (px₁ , px₂) = □⟨ f px₁ ⟩ refl $ px₂

-- 
--   kripke-adjoint : (_∩ P) ⊣ (P ⇛_) 
--   kripke-adjoint .iso = record
--     { to        = kripke-curry ⦃ {!P!} ⦄
--     ; from      = kripke-uncurry
--     ; to-cong   = λ where ≡.refl → ≡.refl
--     ; from-cong = λ where ≡.refl → ≡.refl
--     ; inverse   = (λ x → {!!}) , λ x → {!!}
--     } 
-- 

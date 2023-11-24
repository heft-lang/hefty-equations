import Relation.Unary 

open import Core.Functor 
open import Core.Ternary as Ternary

open import Function hiding (_⟨_⟩_)
open import Level
open import Data.Product

open import Relation.Binary.Bundles
import Relation.Binary.PropositionalEquality as ≡

module Core.Logic {ℓ} (Carrier : Set ℓ) (_∙_≈_ : Rel₃ ℓ ℓ Carrier ) where

open Relation.Unary    
open Ternary.Relation Carrier _∙_≈_
open import Core.MonotonePredicate Carrier _∙_≈_

module Connectives (∙-unitʳ : ∃⟨ RightIdentity ⟩) (∙-assocʳ : RightAssociative) where 

  {- Stars and black holes -} 

  record _✴_ (P Q : Pred Carrier ℓ) (x : Carrier) : Set ℓ where 
    constructor _✴⟨_⟩_
    field
      {c₁ c₂} : Carrier
      px  : P c₁
      sep : c₁ ∙ c₂ ≈ x
      qx  : Q c₂
-- 
--   instance
--     ✴-monotone : Monotone (P ✴ Q)
--     ✴-monotone .weaken (c′ , σ′) (px ✴⟨ σ ⟩ qx) = {!!} 
--   
--     ✴-hmonotoneˡ : ⦃ Monotone P ⦄ → HMonotone (_✴ P)
--     ✴-hmonotoneˡ .T-respects-monotonicity ⦃ m ⦄ .weaken i@(c′ , σ′) (px ✴⟨ σ ⟩ qx) = {!!} 
--     ✴-hmonotoneˡ .transform θ (px ✴⟨ σ ⟩ qx) = θ px ✴⟨ σ ⟩ qx
-- 
--     ✴-hmonotoneʳ : ⦃ Monotone P ⦄ → HMonotone (P ✴_)
--     ✴-hmonotoneʳ .T-respects-monotonicity .weaken i (px ✴⟨ σ ⟩ qx) = {!!} 
--     ✴-hmonotoneʳ .transform θ (px ✴⟨ σ ⟩ qx) = px ✴⟨ σ ⟩ θ qx 
--     
  record _─✴_ (P Q : Pred Carrier ℓ) (x : Carrier) : Set ℓ where
    constructor wand
    field
      _⟨_⟩_ : ∀ {c₁ c₂} → x ∙ c₁ ≈ c₂ → P c₁ → Q c₂
  
  open _✴_
  open _─✴_
  -- 
  -- instance
  --   ─✴-monotone : ⦃ Monotone P ⦄ → ⦃ Monotone Q ⦄ → Monotone (P ─✴ Q)
  --   ─✴-monotone .weaken (_ , σ′) f = wand λ σ x → f ⟨ {!!} ⟩ {!!} 
  -- 
  --   ─✴-hmonotoneˡ : ⦃ Monotone P ⦄ → HMonotone (_─✴ P)
  --   ─✴-hmonotoneˡ = {!!} 
  -- 
  --   ─✴-hmonotoneʳ : ⦃ Monotone P ⦄ → HMonotone (P ─✴_)
  --   ─✴-hmonotoneʳ = {!!} 
  -- 
  record _●_ (P Q  : Pred Carrier ℓ) (x : Carrier) : Set ℓ where
    constructor _●⟨_⟩_
    field
      {c₁ c₂} : Carrier
      px  : P c₁
      sep : x ∙ c₁ ≈ c₂
      qx  : Q c₂
  
  -- If we think of separating conjunction as a transformation that "adds"
  -- resources to its input, the following connective is it's opposite, in the
  -- sense that it describes a transformation that "removes" a resource from its
  -- input.
  record _●─_ (P Q : Pred Carrier ℓ) (x : Carrier) : Set ℓ where
    constructor antiwand 
    field
      _≪_≫_ : ∀ {c₁ c₂} → c₁ ∙ x ≈ c₂ → P c₂ → Q c₁  
  
  open _●─_ 
  
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
  -- ✴-adjoint : ⦃ _ : Monotone P ⦄ → ∀ (P : Pred Carrier ℓ) → (λ Q → Q ✴ {!P!}) ⊣ {!!}
  -- ✴-adjoint = {!!} 
  -- 
  -- A "separating state monad". It is defined as `S ─✴ (P ✴ S)`, but we get it's
  -- monadic structure for free if we define it by going through adjunction that
  -- witnesses the closed monoidal structure of the category of monotone predictes
  -- in terms of ✴/─✴
  -- State✴ : Pred Carrier ℓ → Pred Carrier ℓ → Pred Carrier ℓ
  -- State✴ = M ∘ ✴-adjoint 
  
  ●-curry : ∀[ (P₁ ● P₂) ⇒ Q ] → ∀[ P₁ ⇒ (P₂ ●─ Q) ]
  ●-curry f px₁ = antiwand (λ σ px₂ → f (px₁ ●⟨ σ ⟩ px₂)) 
  
  ●-uncurry : ∀[ P₁ ⇒ (P₂ ●─ Q) ] → ∀[ (P₁ ● P₂) ⇒ Q ]
  ●-uncurry f (px₁ ●⟨ σ ⟩ px₂) = f px₁ ≪ σ ≫ px₂
  
  
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

  □-extract : ∀[ □ P ⇒ P ]
  □-extract px = □⟨ px ⟩ Ext-reflexive ∙-unitʳ

  □-duplicate : ∀[ □ P ⇒ □ (□ P ) ]
  □-duplicate px = necessary λ i → necessary (λ i′ → □⟨ px ⟩ Ext-transitive ∙-assocʳ i i′) 

  mod-curry : ∀[ ◇ P ⇒ Q ] → ∀[ P ⇒ □ Q ]
  mod-curry f px = necessary λ i → f $ ◇⟨ i ⟩ px 
  
  mod-uncurry : ∀[ P ⇒ □ Q ] → ∀[ ◇ P ⇒ Q ]
  mod-uncurry f (◇⟨ i ⟩ px) = □⟨ f px ⟩ i
  -- 
  -- ◇□-adjoint : ◇ ⊣ □
  -- ◇□-adjoint .φ  = mod-curry
  -- ◇□-adjoint .φᵒ = mod-uncurry 
  -- 
  
  --
  -- Anticipation  
  record ◆ (P : Pred Carrier ℓ) (x : Carrier) : Set ℓ where
    constructor ◆⟨_⟩_
    field 
      {x′} : Carrier
      i    : Ext x x′
      px   : P x′ 
  
  open ◆ 
  
  -- Commonality 
  record ■ (P : Pred Carrier ℓ) (x : Carrier) : Set ℓ where
    constructor common
    field
      ■⟨_⟩_ : ∀ {x′} → Ext x′ x → P x′
  
  open ■
  
  mod-curry′ : ∀[ ◆ P ⇒ Q ] → ∀[ P ⇒ ■ Q ]
  mod-curry′ f px = common λ i → f (◆⟨ i ⟩ px)
  
  mod-uncurry′ : ∀[ P ⇒ ■ Q ] → ∀[ ◆ P ⇒ Q ]
  mod-uncurry′ f (◆⟨ i ⟩ px) = ■⟨ f px ⟩ i
  
  open Preorder (Ext-preorder ∙-unitʳ ∙-assocʳ) hiding (Carrier)
  
  -- monotonicity and antitonicity for modalities; An alternative perspective on
  -- these properties is to say that modal propositions are functors over the
  -- (opposite) preorder category of their domain
  -- 
  -- The definitions below are accompanied by comments outlining a temporal
  -- intuition for these properties. But the development here is more general
  -- than that, of course.
  
  -- Weakening of posibility: if we know something is posssible now, we also
  -- know that it will be possible at a later point in time 
  instance ◇-monotone : Monotone (◇ P)
  ◇-monotone .weaken i (◇⟨ i′ ⟩ px) = ◇⟨ trans i′ i ⟩ px
  
  -- Strengthening of anticipation: if we anticipate something to be true at
  -- some point in the future, we could have anticipated the same thing at an
  -- *earlier* point in time
  instance ◈-antitone : Antitone (◆ P)
  ◈-antitone .strengthen i (◆⟨ i′ ⟩ px) = ◆⟨ trans i i′ ⟩ px
  
  -- Weakening of necessity: if something will be necessarily true from this
  -- point in time, it will also be necessarily true in the future
  instance □-monotone : Monotone (□ P)
  □-monotone .weaken i px = necessary (λ i′ → □⟨ px ⟩ trans i i′)
  
  instance ■-antitone : Antitone (■ P)
  ■-antitone .strengthen i px = common λ i′ → ■⟨ px ⟩ trans i′ i
  
  {- A "Kripke closed monoidal structure" on the category of monotone predicates -} 
  
  -- The "Kripke exponent" (or, Kripke function space) between two predicates is
  -- defined as the necessity of their implication.
  _⇛_ : (P Q : Pred Carrier ℓ) → Pred Carrier ℓ
  P ⇛ Q = □ (P ⇒ Q)
  
  kripke-curry : ⦃ _ : Monotone P₁ ⦄ → ∀[ (P₁ ∩ P₂) ⇒ Q ] → ∀[ P₁ ⇒ (P₂ ⇛ Q) ] 
  kripke-curry f px₁ = necessary λ i px₂ → f (weaken i px₁ , px₂) 
  
  kripke-uncurry : ∀[ P₁ ⇒ (P₂ ⇛ Q) ] → ∀[ (P₁ ∩ P₂) ⇒ Q ] 
  kripke-uncurry f (px₁ , px₂) = □⟨ f px₁ ⟩ refl $ px₂
  -- 
  --   kripke-adjoint : (_∩ P) ⊣ (P ⇛_) 
  --   kripke-adjoint .φ  = kripke-curry
  --   kripke-adjoint .φᵒ = kripke-uncurry 
  -- 
  -- 
  --    : ⦃ Monotone P ⦄ → (◇ ∘ (P ∩_)) ⊣ (P ⇒_)
  --   foo .φ  f px′ px = f (◇⟨ refl ⟩ (px , px′))
  --   foo .φᵒ f (◇⟨ i ⟩ (px′ , px)) = f (weaken i px) (weaken i px′)
  -- 

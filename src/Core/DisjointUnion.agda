open import Core.Functor
import Core.Ternary as Ternary


open import Function
open import Function.Construct.Identity using (↔-id)
open import Function.Construct.Composition hiding (inverse)
open import Function.Construct.Symmetry hiding  (inverse)

open import Data.Sum renaming (assocˡ to ⊎-assocˡ ; assocʳ to ⊎-assocʳ)
open import Data.Sum.Properties using (swap-↔)

open import Data.Empty.Polymorphic
open import Data.Unit
open import Data.Product hiding (swap)

open import Level

open import Relation.Unary
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])

module Core.DisjointUnion where

record DisjointUnion {s} (A B C : Set s) : Set s where
  field
    union : (A ⊎ B) ↔ C

  open Inverse
  
  inja = union .to ∘ inj₁ 
  injb = union .to ∘ inj₂
  proj = union .from

  proj∘inja : ∀ a → proj (inja a) ≡ inj₁ a
  proj∘inja a = union .inverse .proj₂ (inj₁ a)

  proj∘injb : ∀ b → proj (injb b) ≡ inj₂ b
  proj∘injb b = union .inverse .proj₂ (inj₂ b)

  {- Much of this turned out not to be necessary. Keep around? -} 
  module _ {ℓ} (P : Pred A ℓ) (Q : Pred B ℓ) where 

    from[_,_] : Pred C ℓ
    from[_,_] = [ P , Q ] ∘ proj

    data From[_,_] (c : C) : Set (s ⊔ ℓ) where
      left  : ∀ x → proj c ≡ inj₁ x → P x → From[_,_] c
      right : ∀ y → proj c ≡ inj₂ y → Q y → From[_,_] c 

    intro-from-a : ∀ {a c} → P a → proj c ≡ inj₁ a → From[_,_] c
    intro-from-a px eq = left _ eq px
    
    intro-from-b : ∀ {b c} → Q b → proj c ≡ inj₂ b → From[_,_] c
    intro-from-b px eq = right _ eq px

open DisjointUnion 
open Inverse


module _ {s : Level} where


  open Ternary.Relation (Set s) DisjointUnion

  disjoint-union-unitˡ : LeftIdentity ⊥ 
  disjoint-union-unitˡ .union = record
    { to        = λ where (inj₂ x) → x
    ; from      = inj₂
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   = (λ _ → refl) , λ where (inj₂ x) → refl
    }

  disjoint-union-unitʳ : RightIdentity ⊥
  disjoint-union-unitʳ .union = record
    { to        = λ where (inj₁ x) → x
    ; from      = inj₁
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   = (λ _ → refl) , λ where (inj₁ x) → refl
    }

  disjoint-union-comm : Commutative 
  disjoint-union-comm u .union = swap-↔ ↔-∘ u .union

  ⊎-congˡ : ∀ {s} {A A′ B : Set s} → A ↔ A′ → (A ⊎ B) ↔ (A′ ⊎ B)
  ⊎-congˡ eq = record
    { to        = [ inj₁ ∘ eq .to , inj₂ ]
    ; from      = [ inj₁ ∘ eq .from , inj₂ ]
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   = ⊎-congˡ-inverseˡ , ⊎-congˡ-inverseʳ
    }
    where
      ⊎-congˡ-inverseˡ : _ 
      ⊎-congˡ-inverseˡ (inj₁ x) = cong inj₁ (eq .inverse .proj₁ x)
      ⊎-congˡ-inverseˡ (inj₂ _) = refl
      
      ⊎-congˡ-inverseʳ : _ 
      ⊎-congˡ-inverseʳ (inj₁ x) = cong inj₁ (eq .inverse .proj₂ x)
      ⊎-congˡ-inverseʳ (inj₂ _) = refl

  ⊎-congʳ : ∀ {s} {A B B′ : Set s} → B ↔ B′ → (A ⊎ B) ↔ (A ⊎ B′)
  ⊎-congʳ eq = record
    { to        = [ inj₁ , inj₂ ∘ eq .to  ]
    ; from      = [ inj₁ , inj₂ ∘ eq .from ]
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   = ⊎-congʳ-inverseˡ , ⊎-congʳ-inverseʳ
    }
    where 
      ⊎-congʳ-inverseˡ : _ 
      ⊎-congʳ-inverseˡ (inj₁ _) = refl
      ⊎-congʳ-inverseˡ (inj₂ y) = cong inj₂ (eq .inverse .proj₁ y)
    
      ⊎-congʳ-inverseʳ : _ 
      ⊎-congʳ-inverseʳ (inj₁ _) = refl
      ⊎-congʳ-inverseʳ (inj₂ y) = cong inj₂ (eq .inverse .proj₂ y)


  disjoint-union-assocʳ : RightAssociative
  disjoint-union-assocʳ {A} {B} {AB} {C} {ABC} u₁ u₂ = (B ⊎ C) , A+BC=ABC , B+C=BC 
    where
      A+BC=ABC : DisjointUnion A (B ⊎ C) ABC
      A+BC=ABC .DisjointUnion.union = ⊎-assoc ↔-∘ (⊎-congˡ (u₁ .union) ↔-∘ u₂ .union)
        where 
          ⊎-assoc : (A ⊎ B ⊎ C) ↔ ((A ⊎ B) ⊎ C)
          ⊎-assoc = record
            { to        = ⊎-assocˡ
            ; from      = ⊎-assocʳ
            ; to-cong   = λ where refl → refl
            ; from-cong = λ where refl → refl
            ; inverse   = ⊎-assoc-inverseˡ , ⊎-assoc-inverseʳ
            }
            where
              ⊎-assoc-inverseˡ : ∀ x → ⊎-assocˡ (⊎-assocʳ x) ≡ x
              ⊎-assoc-inverseˡ (inj₁ (inj₁ _)) = refl
              ⊎-assoc-inverseˡ (inj₁ (inj₂ _)) = refl
              ⊎-assoc-inverseˡ (inj₂ _)        = refl

              ⊎-assoc-inverseʳ : ∀ x → ⊎-assocʳ (⊎-assocˡ x) ≡ x
              ⊎-assoc-inverseʳ (inj₁ _)        = refl
              ⊎-assoc-inverseʳ (inj₂ (inj₁ _)) = refl
              ⊎-assoc-inverseʳ (inj₂ (inj₂ _)) = refl
      
      B+C=BC : DisjointUnion B C (B ⊎ C)
      B+C=BC .DisjointUnion.union = ↔-id _ 
                
  disjoint-union-respects-↔ : Respects _↔_
  disjoint-union-respects-↔ = record
    { r₁ = λ where eq u .union → ⊎-congˡ (↔-sym eq) ↔-∘ u .union
    ; r₂ = λ where eq u .union → ⊎-congʳ (↔-sym eq) ↔-∘ u .union
    ; r₃ = λ where eq u .union → u .union ↔-∘ eq
    }

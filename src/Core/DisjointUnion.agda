open import Core.Functor
open import Core.Ternary Set


open import Function

open import Data.Sum
open import Data.Sum.Properties using (swap-involutive)

open import Data.Empty
open import Data.Unit
open import Data.Product hiding (swap)

open import Relation.Unary
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])

module Core.DisjointUnion where

inj₁-injective : ∀ {x y : A} → inj₁ {B = B} x ≡ inj₁ y → x ≡ y 
inj₁-injective refl = refl

inj₂-injective : ∀ {x y : B} → inj₂ {A = A} x ≡ inj₂ y → x ≡ y
inj₂-injective refl = refl

inj₁≠inj₂ : ∀ {x : A ⊎ B} {y z} → x ≡ inj₁ y → x ≡ inj₂ z → ⊥
inj₁≠inj₂ refl ()

uip : ∀ {a} {A : Set a} {x y : A} → (p q : x ≡ y) → p ≡ q
uip refl refl = refl

record DisjointUnion (A B C : Set) : Set where
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
  module _ {ℓ} (P : Pred A ℓ) (Q : Pred B ℓ) where 

    from[_,_] : Pred C ℓ
    from[_,_] = [ P , Q ] ∘ proj

    data From[_,_] (c : C) : Set ℓ where
      left  : ∀ x → P x → proj c ≡ inj₁ x → From[_,_] c
      right : ∀ y → Q y → proj c ≡ inj₂ y → From[_,_] c 

    intro-from-a : ∀ {a c} → proj c ≡ inj₁ a → P a → From[_,_] c
    intro-from-a eq px = left _ px eq 
    
    intro-from-b : ∀ {b c} → proj c ≡ inj₂ b → Q b → From[_,_] c
    intro-from-b eq qx = right _ qx eq 

    from-elim-a : ∀ {a c} → From[_,_] c → proj c ≡ inj₁ a → P a
    from-elim-a (left  _ px eq) eq′ = subst P (inj₁-injective (trans (sym eq) eq′)) px
    from-elim-a (right _ _  eq) eq′ = ⊥-elim (inj₁≠inj₂ eq′ eq)

    from-elim-b : ∀ {b c} → From[_,_] c → proj c ≡ inj₂ b → Q b
    from-elim-b (left _  _  eq) eq′ = ⊥-elim (inj₁≠inj₂ eq eq′)
    from-elim-b (right _ qx eq) eq′ = subst Q (inj₂-injective (trans (sym eq) eq′)) qx

  from-inv : ∀ c → From[ (λ a → inja a ≡ c) , (λ b → injb b ≡ c) ] c
  from-inv c with proj c | inspect proj c
  ... | inj₁ a | ≡[ eq ]
    = left  a (trans (cong (union .to) (sym eq)) (union .inverse .proj₁ _)) eq
  ... | inj₂ b | ≡[ eq ]
    = right b (trans (cong (union .to) (sym eq)) (union .inverse .proj₁ _)) eq 

  proj-injective : ∀ c₁ c₂ → proj c₁ ≡ proj c₂ → c₁ ≡ c₂
  proj-injective c₁ c₂ eq with from-inv c₁ 
  ... | left  _ refl eq₁ rewrite eq = from-elim-a _ _ (from-inv c₂) eq₁
  ... | right _ refl eq₁ rewrite eq = from-elim-b _ _ (from-inv c₂) eq₁

open DisjointUnion 
open Inverse 

disjoint-union-unitˡ : LeftIdentity DisjointUnion ⊥ 
disjoint-union-unitˡ .union = record
  { to        = λ where (inj₂ x) → x
  ; from      = inj₂
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = (λ _ → refl) , λ where (inj₂ x) → refl
  }

disjoint-union-unitʳ : RightIdentity DisjointUnion ⊥
disjoint-union-unitʳ .union = record
  { to        = λ where (inj₁ x) → x
  ; from      = inj₁
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = (λ _ → refl) , λ where (inj₁ x) → refl
  }

disjoint-union-comm : Commutative DisjointUnion
disjoint-union-comm u .union = record
  { to        = U.union .to ∘ swap
  ; from      = swap ∘ U.union .from
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = comm-inverseˡ , comm-inverseʳ
  }
  where
    module U = DisjointUnion u

    comm-inverseˡ : ∀ x → U.union .to (swap (swap (U.union .from x))) ≡ x
    comm-inverseˡ x =
      begin 
        U.union .to (swap (swap (U.union .from x))) 
      ≡⟨ cong (λ ○ → U.union .to ○) (swap-involutive _) ⟩
        to (U.union) (from (U.union) x)
      ≡⟨ U.union .inverse .proj₁ x ⟩
        x 
      ∎
      where open ≡-Reasoning

    comm-inverseʳ : ∀ x → swap (U.union .from (U.union .to (swap x))) ≡ x 
    comm-inverseʳ x =
      begin
        swap (U.union .from (U.union .to (swap x)))
      ≡⟨ cong swap (U.union .inverse .proj₂ _) ⟩
        swap (swap x)
      ≡⟨ swap-involutive x ⟩
        x
      ∎ 
      where open ≡-Reasoning


disjoint-union-assocʳ : RightAssociative DisjointUnion
disjoint-union-assocʳ {A} {B} {AB} {C} {ABC} u₁ u₂ = BC , A+BC=ABC , B+C=BC 
  where
    module U₁ = DisjointUnion u₁
    module U₂ = DisjointUnion u₂

    Condition : ABC → Set
    Condition = U₂.From[ U₁.From[ ∅ , U ] , U ] 

    cond-irrelevant : Irrelevant Condition
    cond-irrelevant (left x (right y tt eq₁) eq₃) (left x′ (right y′ tt eq₂) eq₄)
      with inj₁-injective (trans (sym eq₄) eq₃)
    cond-irrelevant (left x (right y tt eq₁) eq₃) (left x′ (right y′ tt eq₂) eq₄)
      | refl with inj₂-injective (trans (sym eq₂) eq₁)
    ... | refl = cong₂ (λ ○₁ ○₂ → left x (right y tt ○₁) ○₂) (uip _ _) (uip _ _)
    cond-irrelevant (left _ _ eq₁)   (right _ _ eq₂)   = ⊥-elim (inj₁≠inj₂ eq₁ eq₂)
    cond-irrelevant (right _ tt eq₁) (left _ _ eq₂)    = ⊥-elim (inj₁≠inj₂ eq₂ eq₁)
    cond-irrelevant (right y tt eq)  (right y′ tt eq′)
      with inj₂-injective (trans (sym eq′) eq)
    ... | refl = cong (right y tt) (uip _ _)

    BC : Set
    BC = ∃⟨ Condition ⟩
    
    A→ABC : A → ABC
    A→ABC a = U₂.inja (U₁.inja a)

    B→ABC : B → ABC
    B→ABC b = U₂.inja (U₁.injb b)

    C→ABC : C → ABC
    C→ABC c = U₂.injb c 

    B→BC : B → BC
    B→BC b = B→ABC b , U₂.left (U₁.injb b) (U₁.right b tt (U₁.proj∘injb _)) (U₂.proj∘inja _)

    C→BC : C → BC
    C→BC c = (C→ABC c) , U₂.right c tt (U₂.proj∘injb _) 

    BC→B+C : BC → B ⊎ C
    BC→B+C (abc , left  _ (right b tt eq₁) eq₂) = inj₁ b
    BC→B+C (abc , right c tt               eq ) = inj₂ c

    BC→ABC : BC → ABC
    BC→ABC = proj₁

    ABC→A+BC : ABC → A ⊎ BC
    ABC→A+BC abc with U₂.proj abc
    ABC→A+BC abc | inj₁ ab with U₁.proj ab
    ... | inj₁ a = inj₁ a
    ... | inj₂ b = inj₂ (B→BC b)
    ABC→A+BC abc | inj₂ c  = inj₂ (C→BC c)

    A+BC=ABC : DisjointUnion A BC ABC
    A+BC=ABC .DisjointUnion.union = record
      { to        = [ A→ABC , BC→ABC ]
      ; from      = ABC→A+BC
      ; to-cong   = λ where refl → refl
      ; from-cong = λ where refl → refl
      ; inverse   = U₃-inverseˡ , U₃-inverseʳ
      }
      where
        U₃-inverseˡ : ∀ x → [ A→ABC , BC→ABC ] (ABC→A+BC x) ≡ x
        U₃-inverseˡ x with U₂.from-inv x
        U₃-inverseˡ x | left ab refl eq₁ with U₁.from-inv ab
        ... | left  a refl eq₂ rewrite eq₁ | eq₂ = refl
        ... | right b refl eq₂ rewrite eq₁ | eq₂ = refl
        U₃-inverseˡ x | right c refl eq rewrite eq = refl

        U₃-inverseʳ : ∀ x → ABC→A+BC ([ A→ABC , BC→ABC ] x) ≡ x 
        U₃-inverseʳ (inj₁ a)  with U₂.from-inv (A→ABC a)
        ... | r = {!!} 
        U₃-inverseʳ (inj₂ bc) with U₂.from-inv (BC→ABC bc)
        ... | left ab x₁ x₂ = {!x!}
        ... | right c refl eq rewrite eq = cong inj₂ {!!}


    B+C=BC : DisjointUnion B C BC
    B+C=BC .DisjointUnion.union = record
      { to        = [ B→BC , C→BC ]
      ; from      = BC→B+C
      ; to-cong   = λ where refl → refl
      ; from-cong = λ where refl → refl
      ; inverse   = {!!}
      } 

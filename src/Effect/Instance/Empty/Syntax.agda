open import Core.Functor
open import Core.Container

open import Effect.Base 
open import Effect.Syntax.Free

open import Relation.Unary hiding (Empty)

module Effect.Instance.Empty.Syntax where 

data EmptyC : Set where

Empty : Effect 
Empty = record
  { shape    = EmptyC
  ; position = λ()
  }

extract : Free Empty A → A
extract (pure x) = x

empty′ : Algebraᶜ Empty A
empty′ .αᶜ ()

-- 
-- ♯ᴱ : ∀[ Free ε ⇒ Free (ε ⊕ᶜ Empty) ]
-- ♯ᴱ = ♯ ⦃ ⊑-⊕ᶜ-left Empty ⦄ 
-- 
open import Relation.Binary.PropositionalEquality

extract-lemma : (c : Free Empty A) {v : A} → extract c ≡ v → c ≡ pure v
extract-lemma (pure _) refl = refl

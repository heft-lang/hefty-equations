open import Core.MonotonePredicate 
open import Core.Signature
open import Core.Functor

open import Effect.Base
open import Effect.Syntax.Free
open import Effect.Syntax.Hefty

open import Effect.Handle
open import Effect.Elaborate
open import Effect.Separation
open import Effect.Inclusion
open import Effect.Logic 

open import Effect.Theory.FirstOrder
open import Effect.Theory.HigherOrder

open import Effect.Instance.LocalReader.Syntax
open import Effect.Instance.LocalReader.Theory

open import Effect.Instance.Reader.Syntax
open import Effect.Instance.Reader.Theory
open import Effect.Instance.Reader.Handler

open import Effect.Instance.Empty.Syntax

open import Data.Product
open import Data.Maybe hiding (_>>=_)
open import Data.Sum
open import Data.Unit
open import Data.Empty

open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open import Function
open import Data.Vec hiding ([_])
open import Relation.Unary hiding (Empty ; _⊆_)

module Effect.Instance.LocalReader.Elaboration (R : Set) where

open Connectives

ℋ⟦_⟧ : ⦃ Reader R ≲ ε ⦄ → ∀[ Free ε ⇒ const R ⇒ Free ε ]
ℋ⟦_⟧ ⦃ i ⦄ m r = ♯ ⦃ Reader R , (union-comm $ i .proj₂) ⦄  (handleReader (i .proj₂) m r)

ReaderElab : Elaboration (LocalReader R) (Reader R)
ReaderElab .Elaboration.elab = necessary λ i → readerElab ⦃ i ⦄
  where
    readerElab : ⦃ Reader R ≲ ε ⦄ → Algebra (LocalReader R ε) (Free ε)
    readerElab .α ⟪ `ask ,       k , s ⟫ = ask >>= k
    readerElab .α ⟪ `local _ f , k , s ⟫ = do
      r ← ask 
      v ← ℋ⟦ s tt ⟧ (f r)
      k v
ReaderElab .Elaboration.coherent {c = `ask} k₁ k₂ = sym $ >>=-assoc k₁ k₂ ask
ReaderElab .Elaboration.coherent {c = `local t f} {s = s} ⦃ i ⦄ k₁ k₂ =
  begin
    elab ⟪ `local t f , (k₁ >=> k₂) , s ⟫
  ≡⟨⟩
    (ask >>= λ r → ℋ⟦ s tt ⟧ (f r) >>= (k₁ >=> k₂))
  ≡⟨ (sym $ >>=-assoc (λ r → ℋ⟦ s tt ⟧ (f r)) (k₁ >=> k₂) ask) ⟩
    (ask >>= λ r → ℋ⟦ s tt ⟧ (f r)) >>= (k₁ >=> k₂) 
  ≡⟨ sym $ >>=-assoc k₁ k₂ (ask >>= λ r → ℋ⟦ s tt ⟧ (f r)) ⟩ 
    ((ask >>= λ r → ℋ⟦ s tt ⟧ (f r)) >>= k₁) >>= k₂ 
  ≡⟨ cong (λ ○ → ○ >>= k₂) ((>>=-assoc (λ r → ℋ⟦ s tt ⟧ (f r)) k₁ ask)) ⟩ 
    (ask >>= λ r → ℋ⟦ s tt ⟧ (f r) >>= k₁) >>= k₂ 
  ≡⟨⟩ 
    elab ⟪ `local t f , k₁ , s ⟫ >>= k₂
  ∎
  where
    open ≡-Reasoning 
    elab = (□⟨ Elaboration.elab ReaderElab ⟩ i) .α
 

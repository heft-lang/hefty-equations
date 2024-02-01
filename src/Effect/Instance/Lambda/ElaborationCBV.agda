{-# OPTIONS --type-in-type #-} 

open import Core.Functor
open import Core.Signature
open import Core.Container
open import Core.Extensionality
open import Core.MonotonePredicate 

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

module Effect.Instance.Lambda.ElaborationCBV where

open Connectives

open import Effect.Instance.Lambda.Syntax id (λ A ε B → A → Free ε B)
open import Effect.Instance.Lambda.Theory id (λ A ε B → A → Free ε B) 

LambdaElabCBV : Elaboration Lam ε
LambdaElabCBV .elab = necessary ElabAlg 
  where
    ElabAlg : ε ≲ ε′ → Algebra (Lam ε′) (Free ε′)
    ElabAlg i .α ⟪ `var x , k , _ ⟫ = k x
    ElabAlg i .α ⟪ `abs   , k , s ⟫ = k s
    ElabAlg i .α ⟪ `app f , k , s ⟫ = s tt >>= (f >=> k) 

ℰ⟦_⟧ : ∀[ Hefty (Lam ε) ⇒ Free ε ]  
ℰ⟦_⟧ = fold-hefty pure (□⟨ LambdaElabCBV .elab ⟩ ≲-refl)

CBVCorrect : Correctᴴ LambdaTheory T LambdaElabCBV
CBVCorrect (here refl) T′ sub {γ = f , m} =
  begin
    ℰ⟦ (abs f >>= λ f′ → app f′ m) ⟧
  ≈⟪ {!!} ⟫
    ℰ⟦ abs f ⟧ >>= (λ f′ → ℰ⟦ app f′ m ⟧) 
  ≈⟪⟫
    pure (λ x → ℰ⟦ f x ⟧) >>= (λ f′ → ℰ⟦ app f′ m ⟧)
  ≈⟪⟫
    ℰ⟦ app (ℰ⟦_⟧ ∘ f) m ⟧
  ≈⟪⟫
    ℰ⟦ m ⟧ >>= ((ℰ⟦_⟧ ∘ f) >=> pure)
  ≈⟪ >>=-resp-≈ʳ {m = ℰ⟦ m ⟧} (λ x → >>=-idʳ-≈ ℰ⟦ f x ⟧) ⟫
    ℰ⟦ m ⟧ >>= (λ x → ℰ⟦ f x ⟧)
  ≈⟪ {!!} ⟫ 
    ℰ⟦ m >>= f ⟧
  ∎
  where open ≈-Reasoning T′

CBVCorrect (there (here refl)) T′ sub {γ = f} =
  begin
    ℰ⟦ pure f ⟧
  ≈⟪ ≡-to-≈ (cong (λ ○ → ℰ⟦ pure ○ ⟧) (extensionality $ sym ∘ >>=-idʳ ∘ f)) ⟫
    ℰ⟦ pure (λ x → f x >>= pure) ⟧ 
  ≈⟪⟫ 
    ℰ⟦ pure (λ x → ℰ⟦ var x ⟧ >>= (f >=> pure)) ⟧ 
  ≈⟪⟫ 
    ℰ⟦ pure (λ x → ℰ⟦ app f (var x) ⟧) ⟧ 
  ≈⟪⟫ 
    ℰ⟦ abs (λ x → app f (var x)) ⟧ 
  ∎
  where open ≈-Reasoning T′ 

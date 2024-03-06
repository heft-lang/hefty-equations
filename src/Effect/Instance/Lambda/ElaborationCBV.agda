{-# OPTIONS --type-in-type --without-K #-} 

open import Core.Functor
open import Core.Functor.Monad

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

LambdaElabCBV .Elaboration.elab = necessary ElabAlg 
  where
    ElabAlg : ε ≲ ε′ → Algebra (Lam ε′) (Free ε′)
    ElabAlg i .α ⟪ `var x , k , _ ⟫ = k x
    ElabAlg i .α ⟪ `abs   , k , s ⟫ = k s
    ElabAlg i .α ⟪ `app f , k , s ⟫ = s tt >>= (f >=> k)

LambdaElabCBV .Elaboration.commutes ⟪ `var x , k , s ⟫      = refl
LambdaElabCBV .Elaboration.commutes ⟪ `abs   , k , s ⟫      = refl
LambdaElabCBV .Elaboration.commutes {f = f} ⟪ `app g , k , s ⟫ ⦃ i ⦄ =
  begin
   elab ⟪ `app g , fmap f ∘ k , s ⟫
  ≡⟨⟩ 
    s tt >>= (g >=> (fmap f ∘ k)) 
  ≡⟨ cong (s tt >>=_) (extensionality λ x → sym $ fmap->>= f (g x) k) ⟩ 
    s tt >>= fmap f ∘ (g >=> k)
  ≡⟨ sym (fmap->>= f (s tt) (g >=> k)) ⟩ 
    fmap f (s tt >>= (g >=> k)) 
  ≡⟨⟩ 
    fmap f (elab ⟪ `app g , k , s ⟫)
  ∎
  where
    open ≡-Reasoning
    elab = (□⟨ Elaboration.elab LambdaElabCBV ⟩ i) .α 

LambdaElabCBV .Elaboration.coherent {c = `var x}              k₁ k₂ = refl
LambdaElabCBV .Elaboration.coherent {c = `abs}                k₁ k₂ = refl
LambdaElabCBV .Elaboration.coherent {c = `app f} {s = s} ⦃ i ⦄ k₁ k₂ =
  begin
    elab ⟪ `app f , (k₁ >=> k₂) , s ⟫
  ≡⟨⟩
    s tt >>= (f >=> (k₁ >=> k₂))
  ≡⟨ cong (s tt >>=_) (extensionality λ x → sym $ >>=-assoc k₁ k₂ (f x)) ⟩
    s tt >>= ((f >=> k₁) >=> k₂)
  ≡⟨ sym $ >>=-assoc (f >=> k₁) k₂ (s tt) ⟩
    (s tt >>= (f >=> k₁)) >>= k₂ 
  ≡⟨⟩ 
    elab ⟪ `app f , k₁ , s ⟫ >>= k₂
  ∎
  where
    open ≡-Reasoning
    elab = (□⟨ Elaboration.elab LambdaElabCBV ⟩ i) .α 



CBVCorrect : Correctᴴ LambdaTheory T LambdaElabCBV
CBVCorrect (here refl) T′ sub {γ = f , m} =
  begin
    ℰ⟦ (abs f >>= λ f′ → app f′ m) ⟧
  ≈⟪ ≡-to-≈ $ elab-∘′ (abs f) (λ f′ → app f′ m) ⟫
    ℰ⟦ abs f ⟧ >>= (λ f′ → ℰ⟦ app f′ m ⟧) 
  ≈⟪⟫
    pure (λ x → ℰ⟦ f x ⟧) >>= (λ f′ → ℰ⟦ app f′ m ⟧)
  ≈⟪⟫
    ℰ⟦ app (ℰ⟦_⟧ ∘ f) m ⟧
  ≈⟪⟫
    ℰ⟦ m ⟧ >>= ((ℰ⟦_⟧ ∘ f) >=> pure)
  ≈⟪ >>=-resp-≈ʳ ℰ⟦ m ⟧ (λ x → >>=-idʳ-≈ ℰ⟦ f x ⟧) ⟫
    ℰ⟦ m ⟧ >>= (λ x → ℰ⟦ f x ⟧)
  ≈⟪ ≡-to-≈ (sym $ elab-∘′ m f) ⟫ 
    ℰ⟦ m >>= f ⟧
  ∎
  where
    instance inst : _ ≲ _
    inst = sub .inc
    open ≈-Reasoning T′
    open Elaboration LambdaElabCBV

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
  where
    instance inst : _ ≲ _
    inst = sub .inc
    open ≈-Reasoning T′
    open Elaboration LambdaElabCBV


{-# OPTIONS --type-in-type --without-K --instance-search-dept=2 #-} 

open import Core.Functor
open import Core.Functor.Monad

open import Core.Signature
open import Core.Container
open import Core.Extensionality
open import Core.MonotonePredicate 
open import Core.Ternary
open import Core.Logic

open import Effect.Base
open import Effect.Syntax.Free
open import Effect.Syntax.Hefty

open import Effect.Handle
open import Effect.Elaborate

open import Effect.Theory.FirstOrder
open import Effect.Theory.HigherOrder

open import Effect.Relation.Binary.FirstOrderInclusion
open import Effect.Relation.Ternary.FirstOrderSeparation

open import Effect.Relation.Binary.HigherOrderInclusion
open import Effect.Relation.Ternary.HigherOrderSeparation

open import Effect.Instance.Empty.Syntax

open import Data.Product
open import Data.Maybe hiding (_>>=_)
open import Data.Sum
open import Data.Unit
open import Data.Bool
open import Data.Empty

open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open import Function
open import Data.Vec hiding ([_])
open import Relation.Unary hiding (Empty ; _⊆_)

module Effect.Instance.Lambda.ElaborationCBV where

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

instance refl-inst : ε ≲ ε
refl-inst = ≲-refl 

CBVCorrect : {T : Theory ε} → Correctᴴ LambdaTheory T LambdaElabCBV 
CBVCorrect {T = T} e′ (false , refl) {γ = f , m} =
  begin
    ℰ⟦ (abs f >>= λ f′ → app f′ m) ⟧
  ≈⟪ ≡-to-≈ (elab-∘′ (abs f) λ f′ → app f′ m) ⟫
    ℰ⟦ abs f ⟧ >>= (λ f′ → ℰ⟦ app f′ m ⟧)  
  ≈⟪ >>=-resp-≈ˡ (λ f′ → ℰ⟦ app f′ m ⟧) (≡-to-≈ (use-elab-def _)) ⟫  
    pure ℰ⟪ f ⟫ >>= (λ f′ → ℰ⟦ app f′ m ⟧) 
  ≈⟪⟫
    ℰ⟦ app ℰ⟪ f ⟫ m ⟧
  ≈⟪ ≡-to-≈ (use-elab-def _) ⟫ 
    ℰ⟦ m ⟧ >>= (ℰ⟪ f ⟫ >=> pure) 
  ≈⟪ >>=-resp-≈ʳ ℰ⟦ m ⟧ (>>=-idʳ-≈ ∘ ℰ⟪ f ⟫) ⟫
    ℰ⟦ m ⟧ >>= ℰ⟪ f ⟫  
  ≈⟪ ≡-to-≈ (sym $ elab-∘′ m f) ⟫ 
    ℰ⟦ m >>= f ⟧
  ∎
  where
    open ≈-Reasoning _
    open Elaboration e′
CBVCorrect {T = T} e′ (true  , refl) {γ = f} =
  begin
    ℰ⟦ pure f ⟧
  ≈⟪ ≡-to-≈ (cong (λ ○ → ℰ⟦ pure ○ ⟧) (extensionality $ sym ∘ >>=-idʳ ∘ f)) ⟫
    ℰ⟦ pure (λ x → f x >>= pure) ⟧ 
  ≈⟪ ≡-to-≈ (cong (λ ○ → ℰ⟦ pure (λ x → ○ x >>= (f >=> pure)) ⟧) (extensionality λ x → sym $ use-elab-def _)) ⟫
    ℰ⟦ pure (λ x → ℰ⟦ var x ⟧ >>= (f >=> pure)) ⟧
  ≈⟪ ≡-to-≈ (cong (λ ○ → ℰ⟦ pure ○ ⟧) (extensionality λ x → sym $ use-elab-def _))  ⟫
    ℰ⟦ pure (λ x → ℰ⟦ app f (var x) ⟧) ⟧
  ≈⟪ ≈-sym (≡-to-≈ (use-elab-def _)) ⟫
    ℰ⟦ abs (λ x → app f (var x)) ⟧ 
  ∎
  where
    open ≈-Reasoning _
    open Elaboration e′


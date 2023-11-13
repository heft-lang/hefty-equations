{-# OPTIONS --type-in-type #-} 

open import Core.Functor
open import Core.Signature
open import Core.Container
open import Core.Extensionality

open import Effect.Base
open import Free.Base
open import Hefty.Base 

open import Effect.Theory.FirstOrder
open import Effect.Theory.HigherOrder

open import Effect.Instance.Catch.Syntax
open import Effect.Instance.Catch.Theory

open import Effect.Instance.Abort.Syntax
open import Effect.Instance.Abort.Theory
open import Effect.Instance.Abort.Handler

open import Effect.Instance.Empty.Syntax

open import Data.Product
open import Data.Maybe hiding (_>>=_)
open import Data.Sum
open import Data.Unit

open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Data.Vec hiding ([_])
open import Relation.Unary hiding (Empty)

module Effect.Instance.Catch.Elaboration where


wt : ε ⊑ (ε ⊕ᶜ Empty)
wt = ⊑-⊕ᶜ-left Empty 

CatchElab : Elaboration Catch Abort  
CatchElab .elab .α ⟪ `throw   , r , s ⟫ = abort
CatchElab .elab .α ⟪ `catch A , r , s ⟫ =
  maybe′ r (s (inj₂ tt) >>= r)
    (extract $ handleAbort (♯ ⦃ wt ⦄ (s (inj₁ tt))))

record HandleSem (ε : Effect) (F : Set → Set) : Set where
  field ℋ⟦_⟧ : ∀[ Free ε ⇒ F ]

open HandleSem ⦃...⦄

record ElabSem (η : Effectᴴ) (ε : Effect) : Set where
  field ℰ⟦_⟧ : ∀[ Hefty η ⇒ Free ε ]

open ElabSem ⦃...⦄

instance catchESem : ElabSem Catch Abort
catchESem = record { ℰ⟦_⟧ = elaborate CatchElab }

instance abortHSem : HandleSem Abort Maybe
abortHSem = record { ℋ⟦_⟧ = λ x → extract $ handleAbort (♯ ⦃ wt ⦄ x) }

open ≈-Reasoning AbortTheory

CatchElabCorrect : Correctᴴ CatchTheory AbortTheory CatchElab

CatchElabCorrect (here refl) {_ ∷ _ ∷ []} {k} = begin

    ℰ⟦ throw >>= k ⟧ 
  ≈⟪⟫ {- Definition of throw/bind for Hefty trees -}
    ℰ⟦ throw ⟧
  ∎

CatchElabCorrect (there (here refl)) {_ ∷ []} {m , x}  = 

  begin
    ℰ⟦ catch (pure x) m ⟧ 
  ≈⟪⟫ {- Definition of `elabCatch` -} 
    ℰ⟦ maybe′ pure m ℋ⟦ pure x ⟧ ⟧
  ≈⟪⟫ {- Definitions of `extract` and `handleAbort` -} 
    ℰ⟦ maybe′ pure m (just x) ⟧ 
  ≈⟪⟫ {- Definition of `maybe` -} 
    ℰ⟦ pure x ⟧
  ∎ 


CatchElabCorrect (there (there (here refl))) {A ∷ []} {m} =

  begin
    ℰ⟦ catch throw m ⟧
  ≈⟪⟫ {-  definition of `elaborate` -} 
    fold-hefty pure (CatchElab .elab) (catch throw m)
  ≈⟪⟫ {- definition of `CatchElab` -} 
    maybe′ pure (ℰ⟦ m ⟧ >>= pure) ℋ⟦ abort ⟧
  ≈⟪⟫ {- definition of `extract` and `handleAbort` -} 
    maybe′ pure (ℰ⟦ m ⟧ >>= pure) nothing 
  ≈⟪⟫ {- definition of `maybe` -} 
    ℰ⟦ m ⟧ >>= pure  
  ≈⟪ ≡-to-≈ identity-fold-lemma ⟫ -- TODO: monad laws should be syntactic proofs 
    ℰ⟦ m ⟧
  ∎
  
CatchElabCorrect (there (there (there (here refl)))) {δ = A ∷ []} {m} =

  begin
    ℰ⟦ catch m throw ⟧
  ≈⟪⟫ {- Definition of `elabCatch` -} 
    maybe′ pure (abort >>= pure) ℋ⟦ ℰ⟦ m ⟧ ⟧
  ≈⟪ maybe-lemma just-case (nothing-case m) ⟫
    ℰ⟦ m ⟧
  ∎

  where 
    nothing-case : ∀ m → ℋ⟦ ℰ⟦ m ⟧ ⟧ ≡ nothing → (abort >>= pure) ≈ ℰ⟦ m ⟧
    nothing-case m eq =
      begin
        abort >>= pure
      ≈⟪ ≈-eq′ bind-abort (here refl)  ⟫
        abort
      ≈⟪ adequacy (sym $ extract-lemma _ eq) ⟫
        ℰ⟦ m ⟧
      ∎
      where open Adequacy

    just-case : (x′ : A) → ℋ⟦ ℰ⟦ m ⟧ ⟧ ≡ just x′ → pure x′ ≈ ℰ⟦ m ⟧
    just-case x′ eq =
      begin
        pure x′
      ≈⟪ adequacy (sym $ extract-lemma _ eq) ⟫
        ℰ⟦ m ⟧
      ∎
      where open Adequacy
  
CatchElabCorrect (there (there (there (there (here refl))))) {_ ∷ _ ∷ []} {m₁ , m₂ , k , m₃} =

  begin
    ℰ⟦ catch (catch m₁ m₂ >>= k) m₃ ⟧
  ≈⟪⟫ {- definition of `ℰ⟦_⟧` -} 
    maybe′ pure (ℰ⟦ m₃ ⟧ >>= pure) ℋ⟦ ℰ⟦ catch m₁ m₂ >>= k ⟧ ⟧
  ≈⟪⟫ {- Definition of `ℰ⟦_⟧` -} 
    maybe′ pure (ℰ⟦ m₃ ⟧ >>= pure) ℋ⟦ maybe′ (ℰ⟦_⟧ ∘ k) (ℰ⟦ m₂ >>= pure ⟧ >>= (ℰ⟦_⟧ ∘ k)) ℋ⟦ ℰ⟦ m₁ >>= pure ⟧ ⟧ ⟧
  ≈⟪ {!!}  ⟫ 
    maybe′ pure (maybe′ pure (ℰ⟦ m₃ ⟧ >>= pure) ℋ⟦ ℰ⟦ m₂ >>= k ⟧ ⟧ >>= pure) ℋ⟦ ℰ⟦ m₁ >>= k ⟧ ⟧
  ≈⟪⟫ {- Definition of `ℰ⟦_⟧` -} 
    maybe′ pure (ℰ⟦ catch (m₂ >>= k) m₃ ⟧ >>= pure) ℋ⟦ ℰ⟦ m₁ >>= k ⟧ ⟧
  ≈⟪⟫ {- Definition of `ℰ⟦_⟧` -} 
    ℰ⟦ catch (m₁ >>= k) (catch (m₂ >>= k) m₃) ⟧
  ∎


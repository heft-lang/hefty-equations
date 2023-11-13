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


elabCatch : ∀[ Hefty Catch ⇒ Free Abort ]
elabCatch = elaborate CatchElab 

open ≈-Reasoning AbortTheory

CatchElabCorrect : Correctᴴ CatchTheory AbortTheory CatchElab

CatchElabCorrect (here refl) {_ ∷ _ ∷ []} {k} = begin

    elabCatch (throw >>= k) 
  ≈⟪⟫ {- Definition of throw/bind for Hefty trees -}
    elabCatch throw
  ∎
  
CatchElabCorrect (there (here refl)) {_ ∷ []} {m , x}  = 

  begin
    elabCatch (catch (return x) m) 
  ≈⟪⟫ {- Definition of `elabCatch` -} 
    elabCatch (maybe′ pure m (extract $ handleAbort (♯ (return x))))
  ≈⟪⟫ {- Definitions of `extract` and `handleAbort` -} 
    elabCatch (maybe′ pure m (just x)) 
  ≈⟪⟫ {- Definition of `maybe` -} 
    elabCatch (return x)
  ∎ 

CatchElabCorrect (there (there (here refl))) {A ∷ []} {m} =

  begin
    elabCatch (catch throw m)
  ≈⟪⟫ {-  definition of `elaborate` -} 
    fold-hefty pure (CatchElab .elab) (catch throw m)
  ≈⟪⟫ {- definition of `CatchElab` -} 
    maybe′ pure (⦅ pure , impure′ ⦆ (elabCatch m)) (extract $ handleAbort (♯ ⦃ wt ⦄ abort)) 
  ≈⟪⟫ {- definition of `extract` and `handleAbort` -} 
    maybe′ pure (⦅ pure , impure′ ⦆ (elabCatch m)) nothing 
  ≈⟪⟫ {- definition of `maybe` -} 
    (⦅ pure , impure′ ⦆ (elabCatch m)) 
  ≈⟪ ≡-to-≈ identity-fold-lemma ⟫ 
    elabCatch m
  ∎
  
CatchElabCorrect (there (there (there (here refl)))) {δ = A ∷ []} {m} =

  begin
    elabCatch (catch m throw)
  ≈⟪⟫ {- Definition of `elabCatch` -} 
    maybe′ pure (abort >>= pure) (extract $ handleAbort (♯ ⦃ wt ⦄ (elabCatch m)))
  ≈⟪ maybe-lemma just-case (nothing-case m) ⟫
    elabCatch m
  ∎

  where 
    nothing-case : ∀ m → extract (handleAbort (♯ ⦃ wt ⦄ (elabCatch m))) ≡ nothing → (abort >>= pure) ≈ elabCatch m
    nothing-case m eq =
      begin
        (abort >>= pure)
      ≈⟪ ≈-eq′ bind-abort (here refl)  ⟫
        abort
      ≈⟪ adequacy (sym $ extract-lemma _ eq) ⟫
        elabCatch m 
      ∎
      where open Adequacy

    just-case : (x′ : A) → extract (handleAbort (♯ ⦃ wt ⦄ (elabCatch m))) ≡ just x′ → pure x′ ≈ elabCatch m
    just-case x′ eq =
      begin
        pure x′
      ≈⟪ adequacy (sym $ extract-lemma _ eq) ⟫
        elabCatch m
      ∎
      where open Adequacy
  
CatchElabCorrect (there (there (there (there (here refl))))) {_ ∷ _ ∷ []} {m₁ , m₂ , k , m₃} = {!!}

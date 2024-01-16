{-# OPTIONS --type-in-type --allow-unsolved-metas #-} 

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
open import Data.Empty

open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open import Function
open import Data.Vec hiding ([_])
open import Relation.Unary hiding (Empty ; _⊆_)

module Effect.Instance.Catch.Elaboration where

open Connectives

ℋ⟦_⟧ : ⦃ Abort ≲ ε ⦄ → ∀[ Free ε ⇒ Maybe ⊢ Free ε ]
ℋ⟦_⟧ ⦃ i ⦄ = ♯ ⦃ Abort , (union-comm $ i .proj₂) ⦄  ∘ handleAbort (i .proj₂)

CatchElab : Elaboration Catch Abort
CatchElab .elab = necessary λ i → CatchElabAlg ⦃ i ⦄
  where
    CatchElabAlg : ⦃ Abort ≲ ε ⦄ → Algebra Catch (Free ε)
    CatchElabAlg .α ⟪ `throw   , k , s ⟫ = abort
    CatchElabAlg .α ⟪ `catch A , k , s ⟫ = do
      v ← ℋ⟦ (s (inj₁ tt)) ⟧
      maybe′ k (s (inj₂ tt) >>= k) v


-- 
-- elab-respects-bind : ∀ c r s (k : A → Free Abort B) → CatchElab .elab .α ⟪ c , r , s ⟫ >>= k ≡ CatchElab .elab .α ⟪ c , (_>>= k) ∘ r , s ⟫
-- elab-respects-bind `throw r s k = {!!}
-- elab-respects-bind (`catch t) r s k = {!!}
--


ℰ⟦_⟧ : ⦃ Abort ≲ ε ⦄ → ∀[ Hefty Catch ⇒ Free ε ]  
ℰ⟦_⟧ ⦃ i ⦄ = fold-hefty pure (□⟨ CatchElab .elab ⟩ i)



CatchElabCorrect : Correctᴴ CatchTheory AbortTheory CatchElab
CatchElabCorrect px {ε′ = ε′} ⦃ i ⦄ T′ sub {γ = k} = go px sub 
  where
    open ≈-Reasoning T′
    instance inst : proj₁ i ≲ ε′
    inst = _ , (union-comm $ proj₂ i)


    go : ∀ {eq : Equationᴴ _}
         → eq ◃ᴴ CatchTheory
         → AbortTheory ⊆⟨ i ⟩ T′
           -------------------------------------------------
         → Respectsᴴ (_≈⟨ T′ ⟩_) (□⟨ CatchElab .elab ⟩ i) eq


    -- bind-throw 
    go (here refl) _ {γ = k} =
    
      begin
        ℰ⟦ throw >>= k ⟧
      ≈⟪⟫ {- Definition of >>= and throw -}
        abort 
      ≈⟪⟫ {- Definition of throw -} 
        ℰ⟦ throw ⟧
      ∎
      
    -- catch-return 
    go (there (here refl)) sub {γ = m , x} =
      begin
        ℰ⟦ catch (return x) m ⟧
      ≈⟪⟫ {- Definition of catch -} 
         ℋ⟦ return x ⟧ >>= (λ v → ℰ⟦ maybe′ return m v ⟧)
      ≈⟪⟫ {- Definition of abort handler -} 
        pure x >>= (λ v → ℰ⟦ maybe′ return m (just v) ⟧)
      ≈⟪⟫ {- Definition of >>= -} 
        ℰ⟦ maybe′ return m (just x) ⟧
      ≈⟪⟫ {- Definition of maybe′ -} 
        ℰ⟦ return x ⟧
      ∎

    -- catch-throw-1 
    go (there (there (here refl))) sub {δ = A , _} {γ = m} =
      begin
        ℰ⟦ catch throw m ⟧
      ≈⟪⟫ {- definition of ℰ⟦-⟧ -} 
        ℋ⟦ ℰ⟦ throw ⟧ ⟧ >>= maybe′ pure (ℰ⟦ m ⟧ >>= pure)
      ≈⟪⟫ {- -} 
        ℋ⟦ abort ⟧ >>= maybe′ pure (ℰ⟦ m ⟧ >>= pure) 
      ≈⟪ ≡-to-≈ (cong (λ ○ → ○ >>= λ v → maybe′ pure (ℰ⟦ m ⟧ >>= pure) v) ℋ-lemma) ⟫
        pure nothing >>= maybe′ pure (ℰ⟦ m ⟧ >>= pure)
      ≈⟪⟫ {- Definition of >>= and maybe′ -} 
        ℰ⟦ m ⟧ >>= pure 
      ≈⟪ ≡-to-≈ identity-fold-lemma ⟫ 
        ℰ⟦ m ⟧
      ∎
      where
        open ≡-Reasoning renaming (begin_ to ≡-begin_ ; _∎ to _QED) 

        ℋ-lemma : ℋ⟦ abort ⟧ ≡ pure nothing 
        ℋ-lemma =
          ≡-begin
            ℋ⟦ abort ⟧
          ≡⟨⟩
            ♯ ⦃ Abort , union-comm (i .proj₂) ⦄ (handleAbort (i .proj₂) abort)
          ≡⟨ cong (♯ ⦃ Abort , union-comm (i .proj₂) ⦄) (Properties.handle-abort-is-nothing (i .proj₂)) ⟩ 
            ♯ ⦃ Abort , union-comm (i .proj₂) ⦄ (pure nothing) 
          ≡⟨⟩
            pure nothing
          QED


    {- catch-throw-2 -} 
    go (there (there (there (here refl)))) sub {γ = m} =
      begin
        ℰ⟦ catch m throw ⟧
      ≈⟪⟫ {- Definition of elabCatch -}  
        ℋ⟦ ℰ⟦ m ⟧ ⟧ >>= maybe′ pure (ℰ⟦ throw ⟧ >>= pure) 
      ≈⟪ {!!} ⟫ 
        ℰ⟦ m ⟧
      ∎

    {- catch-catch -} 
    go (there (there (there (there (here refl))))) sub = {!!}

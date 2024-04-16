{-# OPTIONS --without-K --type-in-type #-} 

open import Core.Functor
open import Core.Functor.Monad
open import Core.Functor.NaturalTransformation
open import Core.Ternary
open import Core.Logic

open import Core.Signature
open import Core.Container
open import Core.Extensionality
open import Core.MonotonePredicate 

open import Effect.Base
open import Effect.Syntax.Free
open import Effect.Syntax.Hefty

open import Effect.Handle
open import Effect.Elaborate

open import Effect.Relation.Binary.FirstOrderInclusion
open import Effect.Relation.Binary.HigherOrderInclusion
open import Effect.Relation.Ternary.FirstOrderSeparation
open import Effect.Relation.Ternary.HigherOrderSeparation

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
open import Data.Fin

open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open import Function
open import Data.Vec hiding ([_])
open import Relation.Unary hiding (Empty ; _⊆_)

module Effect.Instance.Catch.Elaboration where

open Handler AbortHandler


CatchElab : Elaboration Catch Abort
CatchElab .Elaboration.elab = necessary λ i → CatchElabAlg ⦃ i ⦄
  where
    CatchElabAlg : ⦃ Abort ≲ ε ⦄ → Algebra (Catch ε) (Free ε)
    CatchElabAlg .α ⟪ `throw   , k , s ⟫ = abort
    CatchElabAlg .α ⟪ `catch A , k , s ⟫ = do
      v ← ℋ⟦ (s (inj₁ tt)) ⟧ tt
      maybe′ k (s (inj₂ tt) >>= k) v

CatchElab .Elaboration.commutes {f = f} ⟪ `throw   , k , s ⟫ ⦃ i ⦄ = 
  begin
    abort 
  ≡⟨⟩
    impure (inj ⟨ `abort , ♯ ∘ ⊥-elim ⟩)
  ≡⟨ cong (λ ○ → impure (inj ⟨ `abort , ○ ⟩)) (extensionality λ()) ⟩
    impure (inj ⟨ `abort , fmap (fmap {F = Free _} f) ∘ ♯ ∘ ⊥-elim ⟩) 
  ≡⟨ (cong impure $ inj-natural .commute {f = fmap f} ⟨ `abort , ♯ ∘ ⊥-elim ⟩) ⟩ 
    impure (fmap (fmap {F = Free _} f) (inj ⟨ (`abort , ♯ ∘ ⊥-elim) ⟩))
  ≡⟨⟩ 
    fmap f (impure (inj ⟨ `abort , ♯ ∘ ⊥-elim ⟩)) 
  ≡⟨⟩ 
    fmap f abort
  ∎
  where
    open ≡-Reasoning
    elab = (□⟨ Elaboration.elab CatchElab ⟩ i) .α 

CatchElab .Elaboration.commutes {f = f} ⟪ `catch t , k , s ⟫ ⦃ i ⦄ =
  begin
    elab ⟪ `catch t , fmap f ∘ k , s ⟫
  ≡⟨⟩ 
    ℋ⟦ s (inj₁ tt) ⟧ tt >>= maybe′ (fmap f ∘ k) (s (inj₂ tt) >>= fmap f ∘ k) 
  ≡⟨ cong (λ ○ → ℋ⟦ s (inj₁ tt) ⟧ tt >>= maybe′ (fmap f ∘ k) ○) (sym (fmap->>= f (s (inj₂ tt)) k)) ⟩
    ℋ⟦ s (inj₁ tt) ⟧ tt >>= maybe′ (fmap f ∘ k) (fmap f (s (inj₂ tt) >>= k)) 
  ≡⟨ cong (ℋ⟦ s (inj₁ tt) ⟧ tt >>=_) (extensionality $ sym ∘ fmap-maybe k (s (inj₂ tt) >>= k)) ⟩ 
    ℋ⟦ s (inj₁ tt) ⟧ tt >>= fmap f ∘ maybe′ k (s (inj₂ tt) >>= k) 
  ≡⟨ sym (fmap->>= f (ℋ⟦ s (inj₁ tt) ⟧ tt) (maybe′ k (s (inj₂ tt) >>= k))) ⟩ 
    fmap f (ℋ⟦ s (inj₁ tt) ⟧ tt >>= maybe′ k (s (inj₂ tt) >>= k)) 
  ≡⟨⟩ 
    fmap f (elab ⟪ `catch t , k , s ⟫)
  ∎
  where
    open ≡-Reasoning
    elab = (□⟨ Elaboration.elab CatchElab ⟩ i) .α

    fmap-maybe :
      ∀ (j : A → Free ε _) (n : Free ε _) x
      → fmap f (maybe′ j n x) ≡ maybe′ (fmap f ∘ j) (fmap f n) x
    fmap-maybe j n (just x) = refl
    fmap-maybe j n nothing  = refl
      
CatchElab .Elaboration.coherent {ε′ = ε′} {c = `throw} {s = s} ⦃ i ⦄   k₁ k₂ =
  begin
    elab ⟪ `throw , (k₁ >=> k₂) , s ⟫
  ≡⟨⟩
    abort
  ≡⟨⟩ 
    impure (inj ⟨ `abort , ♯ ∘ ⊥-elim ⟩)
  ≡⟨ cong (λ ○ → impure (inj ⟨ `abort , ○ ⟩)) (extensionality λ()) ⟩
    impure (inj (fmap {F = ⟦ Abort ⟧ᶜ} (_>>= k₂) ⟨ `abort , ♯ ∘ ⊥-elim ⟩)) 
  ≡⟨ cong impure (inj-natural .commute {f = _>>= k₂} _) ⟩ 
    impure (fmap {F = ⟦ ε′ ⟧ᶜ} (_>>= k₂) (inj ⟨ `abort , ♯ ∘ ⊥-elim ⟩)) 
  ≡⟨⟩ 
    impure (inj ⟨ `abort , ♯ ∘ ⊥-elim ⟩) >>= k₂ 
  ≡⟨⟩ 
    abort >>= k₂
  ≡⟨⟩ 
    elab ⟪ `throw , k₁ , s ⟫ >>= k₂
  ∎
  where
    open ≡-Reasoning
    elab = (□⟨ Elaboration.elab CatchElab ⟩ i) .α 
CatchElab .Elaboration.coherent {ε′ = ε′} {c = `catch t} {s = s} ⦃ i ⦄  k₁ k₂ =
  begin
    elab ⟪ `catch t , (k₁ >=> k₂) , s ⟫
  ≡⟨⟩
    ℋ⟦ s (inj₁ tt) ⟧ tt >>= maybe′ (k₁ >=> k₂) (s (inj₂ tt) >>= (k₁ >=> k₂))
  ≡⟨ cong (λ ○ → ℋ⟦ s (inj₁ tt) ⟧ tt >>= maybe′ (k₁ >=> k₂) ○) (sym (>>=-assoc k₁ k₂ (s (inj₂ tt)))) ⟩ 
    ℋ⟦ s (inj₁ tt) ⟧ tt >>= maybe′ (k₁ >=> k₂) ((s (inj₂ tt) >>= k₁) >>= k₂) 
  ≡⟨ cong (λ ○ → ℋ⟦ s (inj₁ tt) ⟧ tt >>= ○) (extensionality $ maybe (λ _ → refl) refl) ⟩
    ℋ⟦ s (inj₁ tt) ⟧ tt >>= (maybe′ k₁ (s (inj₂ tt) >>= k₁) >=> k₂) 
  ≡⟨ sym (>>=-assoc (maybe′ k₁ (s (inj₂ tt) >>= k₁)) k₂ $ ℋ⟦ s (inj₁ tt) ⟧ tt) ⟩ 
    (ℋ⟦ s (inj₁ tt) ⟧ tt >>= maybe′ k₁ (s (inj₂ tt) >>= k₁)) >>= k₂ 
  ≡⟨⟩ 
    elab ⟪ `catch t , k₁ , s ⟫ >>= k₂
  ∎
  where
    open ≡-Reasoning
    elab = (□⟨ Elaboration.elab CatchElab ⟩ i) .α

instance refl-inst : ε ≲ ε
refl-inst = ≲-refl 

CatchElabCorrect : □-Correctᴴ CatchTheory AbortTheory CatchElab
CatchElabCorrect e′ ⦃ ζ ⦄ (zero , refl) {γ = k}  =
  begin
    ℰ⟦ throw >>= k ⟧
  ≈⟪ ≡-to-≈ $ elab-∘′ throw k ⟫ 
    ℰ⟦ throw ⟧ >>= ℰ⟪ k ⟫ 
  ≈⟪ >>=-resp-≈ˡ ℰ⟪ k ⟫ (≡-to-≈ (use-elab-def _)) ⟫ 
    abort >>= ℰ⟪ k ⟫
  ≈⟪ ≈-eq′ bind-abort (here refl) ⟫
    abort 
  ≈⟪ ≈-sym (≡-to-≈ (use-elab-def _)) ⟫ 
    ℰ⟦ throw ⟧
  ∎
  where
    open ≈-Reasoning (□⟨ AbortTheory .theory ⟩ ζ .≲-eff)
    open Elaboration e′
  
CatchElabCorrect e′ ⦃ ζ ⦄ (suc zero , refl) {γ = m , x} = 
  begin
    ℰ⟦ catch (return x) m ⟧
  ≈⟪ ≡-to-≈ (use-elab-def _) ⟫
    ℋ⟦ return x ⟧ tt >>= (λ v → ℰ⟦ maybe′ return m v ⟧)
  ≈⟪⟫
    pure x >>= ((λ v → ℰ⟦ maybe′ return m (just v) ⟧)) 
  ≈⟪⟫
    ℰ⟦ maybe′ return m (just x) ⟧ 
  ≈⟪⟫ 
    ℰ⟦ return x ⟧
  ∎
  where
    open ≈-Reasoning (□⟨ AbortTheory .theory ⟩ ζ .≲-eff)
    open Elaboration e′

CatchElabCorrect e′ ⦃ ζ ⦄ (suc (suc zero) , refl) {γ = m} =

  begin
    ℰ⟦ catch throw m ⟧
  ≈⟪ ≡-to-≈ (use-elab-def _) ⟫
    ℋ⟦ ℰ⟦ throw ⟧ ⟧ tt >>= maybe′ pure (ℰ⟦ m ⟧ >>= pure) 
  ≈⟪ >>=-resp-≈ˡ (maybe′ pure (ℰ⟦ m ⟧ >>= pure)) (≡-to-≈ $ cong (λ ○ → ℋ⟦ ○ ⟧ tt) (use-elab-def _)) ⟫
    ℋ⟦ abort ⟧ tt >>= maybe′ pure (ℰ⟦ m ⟧ >>= pure)
  ≈⟪ >>=-resp-≈ˡ _ (≡-to-≈ ℋ-lemma) ⟫
    pure nothing >>= maybe′ pure (ℰ⟦ m ⟧ >>= pure)
  ≈⟪⟫ {- Definition of >>= and maybe′ -} 
    ℰ⟦ m ⟧ >>= pure 
  ≈⟪ ≡-to-≈ identity-fold-lemma ⟫   
    ℰ⟦ m ⟧
  ∎
  where
    open ≈-Reasoning (□⟨ AbortTheory .theory ⟩ ζ .≲-eff)
    open Elaboration e′

    ℋ-lemma : ℋ⟦ abort ⟧ tt ≡ pure nothing 
    ℋ-lemma =
      ≡-begin
        ℋ⟦ abort ⟧ tt
      ≡⟨⟩
        ♯ ⦃ Abort , union-comm (ζ .≲-eff .proj₂) ⦄ (handleAbort ((ζ .≲-eff .proj₂)) abort)
      ≡⟨ cong (♯ ⦃ Abort , union-comm ((ζ .≲-eff .proj₂)) ⦄) (Properties.handle-abort-is-nothing ((ζ .≲-eff .proj₂))) ⟩ 
        ♯ ⦃ Abort , union-comm ((ζ .≲-eff .proj₂)) ⦄ (pure nothing) 
      ≡⟨⟩
        pure nothing
      QED
      where
        open ≡-Reasoning renaming (begin_ to ≡-begin_ ; _∎ to _QED) 

CatchElabCorrect e′ ⦃ ζ ⦄ (suc (suc (suc zero)) , refl) {γ = m} = 
  begin
    ℰ⟦ catch m throw ⟧
  ≈⟪ ≡-to-≈ (use-elab-def _) ⟫ {- Definition of elabCatch -}  
    ℋ⟦ ℰ⟦ m ⟧ ⟧ tt >>= maybe′ pure (ℰ⟦ throw ⟧ >>= pure)
  ≈⟪ >>=-resp-≈ʳ (ℋ⟦ ℰ⟦ m ⟧ ⟧ tt) (λ x → ≡-to-≈ (cong (λ ○ → maybe′ pure (○ >>= pure) x) (use-elab-def _))) ⟫
    ℋ⟦ ℰ⟦ m ⟧ ⟧ tt >>= maybe′ pure (abort >>= pure)  
  ≈⟪ ≡-to-≈ $ Properties.catch-throw-lemma ℰ⟦ m ⟧ ⟫ 
    ℰ⟦ m ⟧
  ∎
  where
    open ≈-Reasoning (□⟨ AbortTheory .theory ⟩ ζ .≲-eff)
    open Elaboration e′

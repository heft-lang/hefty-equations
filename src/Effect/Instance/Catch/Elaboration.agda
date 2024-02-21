{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Functor.Monad
open import Core.Functor.NaturalTransformation

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
CatchElab .Elaboration.elab = necessary λ i → CatchElabAlg ⦃ i ⦄
  where
    CatchElabAlg : ⦃ Abort ≲ ε ⦄ → Algebra (Catch ε) (Free ε)
    CatchElabAlg .α ⟪ `throw   , k , s ⟫ = abort
    CatchElabAlg .α ⟪ `catch A , k , s ⟫ = do
      v ← ℋ⟦ (s (inj₁ tt)) ⟧
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
    ℋ⟦ s (inj₁ tt) ⟧ >>= maybe′ (fmap f ∘ k) (s (inj₂ tt) >>= fmap f ∘ k) 
  ≡⟨ cong (λ ○ → ℋ⟦ s (inj₁ tt) ⟧ >>= maybe′ (fmap f ∘ k) ○) (sym (fmap->>= f (s (inj₂ tt)) k)) ⟩
    ℋ⟦ s (inj₁ tt) ⟧ >>= maybe′ (fmap f ∘ k) (fmap f (s (inj₂ tt) >>= k)) 
  ≡⟨ cong (ℋ⟦ s (inj₁ tt) ⟧ >>=_) (extensionality $ sym ∘ fmap-maybe k (s (inj₂ tt) >>= k)) ⟩ 
    ℋ⟦ s (inj₁ tt) ⟧ >>= fmap f ∘ maybe′ k (s (inj₂ tt) >>= k) 
  ≡⟨ sym (fmap->>= f ℋ⟦ s (inj₁ tt) ⟧ (maybe′ k (s (inj₂ tt) >>= k))) ⟩ 
    fmap f (ℋ⟦ s (inj₁ tt) ⟧ >>= maybe′ k (s (inj₂ tt) >>= k)) 
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
    ℋ⟦ s (inj₁ tt) ⟧ >>= maybe′ (k₁ >=> k₂) (s (inj₂ tt) >>= (k₁ >=> k₂))
  ≡⟨ cong (λ ○ → ℋ⟦ s (inj₁ tt) ⟧ >>= maybe′ (k₁ >=> k₂) ○) (sym (>>=-assoc k₁ k₂ (s (inj₂ tt)))) ⟩ 
    ℋ⟦ s (inj₁ tt) ⟧ >>= maybe′ (k₁ >=> k₂) ((s (inj₂ tt) >>= k₁) >>= k₂) 
  ≡⟨ cong (λ ○ → ℋ⟦ s (inj₁ tt) ⟧ >>= ○) (extensionality $ maybe (λ _ → refl) refl) ⟩
    ℋ⟦ s (inj₁ tt) ⟧ >>= (maybe′ k₁ (s (inj₂ tt) >>= k₁) >=> k₂) 
  ≡⟨ sym (>>=-assoc (maybe′ k₁ (s (inj₂ tt) >>= k₁)) k₂ ℋ⟦ s (inj₁ tt) ⟧) ⟩ 
    (ℋ⟦ s (inj₁ tt) ⟧ >>= maybe′ k₁ (s (inj₂ tt) >>= k₁)) >>= k₂ 
  ≡⟨⟩ 
    elab ⟪ `catch t , k₁ , s ⟫ >>= k₂
  ∎
  where
    open ≡-Reasoning
    elab = (□⟨ Elaboration.elab CatchElab ⟩ i) .α

-- TODO: explain why we need to disable the termination checker here, and why we
-- think this is okay
{-# TERMINATING #-}
CatchElabCorrect : Correctᴴ CatchTheory AbortTheory CatchElab
CatchElabCorrect px {ε′ = ε′} ⦃ i ⦄ T′ sub {γ = k} = go px sub 
  where
    open ≈-Reasoning T′
    open Elaboration CatchElab
    instance inst : proj₁ i ≲ ε′
    inst = _ , (union-comm $ proj₂ i)


    go : ∀ {eq : Equationᴴ _}
         → eq ◃ᴴ CatchTheory
         → AbortTheory ⊆⟨ i ⟩ T′
           --------------------------------------
         → Respectsᴴ (_≈⟨ T′ ⟩_) (□⟨ elab ⟩ i) eq

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
      ≈⟪ >>=-resp-≈ˡ _ (≡-to-≈ ℋ-lemma) ⟫
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
      ≈⟪⟫
        ℋ⟦ ℰ⟦ m ⟧ ⟧ >>= maybe′ pure (abort >>= pure)  
      ≈⟪ ≡-to-≈ $ catch-throw-lemma ℰ⟦ m ⟧ ⟫ 
        ℰ⟦ m ⟧
      ∎
      where

        open Union (i .proj₂)
        open ≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _QED) 

        catch-throw-lemma : ∀ (m : Free ε′ A) → ℋ⟦ m ⟧ >>= maybe′ pure (abort >>= pure) ≡ m
        catch-throw-lemma (pure x)               = refl
        catch-throw-lemma (impure v@(⟨ c , k ⟩)) with proj v | inspect proj v
        ... | ⟨ inj₁ `abort , k′ ⟩ | ≡[ eq ] =
          ≡-begin
            ℋ⟦ impure v ⟧ >>= f
          ≡⟨⟩
            ♯ (handle′ AbortHandler tt (impure (proj (fmap (separate (i .proj₂)) v)))) >>= f
          ≡⟨ cong (λ ○ → ♯ (handle′ AbortHandler tt (impure ○)) >>= f) (proj-natural .commute {f = separate (i .proj₂)} _) ⟩
            ♯ (handle′ AbortHandler tt (impure (fmap (separate (i .proj₂)) (proj v)))) >>= f
          ≡⟨ cong (λ ○ → ♯ (handle′ AbortHandler tt (impure (fmap (separate (i .proj₂)) ○))) >>= f) eq ⟩
            ♯ (handle′ AbortHandler tt (impure (fmap (separate (i .proj₂)) ⟨ inj₁ `abort , k′ ⟩))) >>= f
          ≡⟨⟩ {- simplify -} 
            abort >>= pure
          ≡⟨ >>=-idʳ abort ⟩
            abort 
          ≡⟨⟩ 
            impure (inj ⟨ `abort , ♯ ∘ ⊥-elim ⟩) 
          ≡⟨ cong (λ ○ → impure (inj ⟨ `abort , ○ ⟩)) (extensionality (λ())) ⟩ 
            impure (inja ⟨ `abort , k′ ⟩)  
          ≡⟨ cong impure (sym (proj-injˡ _ _ eq)) ⟩
            impure v
          QED

          where
            f = maybe′ pure (abort >>= pure)
            
        ... | ⟨ inj₂ c′ , k′ ⟩ | ≡[ eq ] =

          ≡-begin
            ℋ⟦ impure ⟨ c , k ⟩ ⟧ >>= f
          ≡⟨⟩ {- inline definition -} 
            ♯ (handle′ AbortHandler tt (impure (proj (fmap (separate (i .proj₂)) v)))) >>= f
          ≡⟨ cong (λ ○ → ♯ (handle′ AbortHandler tt (impure ○)) >>= f) (proj-natural .commute {f = separate (i .proj₂)} _)⟩
            ♯ (handle′ AbortHandler tt (impure (fmap (separate (i .proj₂)) (proj v)))) >>= f
          ≡⟨ cong (λ ○ → ♯ (handle′ AbortHandler tt (impure (fmap (separate (i .proj₂)) ○))) >>= f) eq ⟩
            ♯ (handle′ AbortHandler tt (impure (fmap (separate (i .proj₂)) ⟨ inj₂ c′ , k′ ⟩))) >>= f
          ≡⟨⟩ {- simplify -} 
            impure (injb ⟨ c′ , ℋ⟦_⟧ ∘ k′ ⟩) >>= f
          ≡⟨⟩ {- definition of >>= -} 
            impure (fmap ⦃ con-functor ⦄ (_>>= f) (injb ⟨ c′ , ℋ⟦_⟧ ∘ k′ ⟩)) 
          ≡⟨ cong impure (sym $ injb-natural .commute {f = _>>= f} _) ⟩
            impure (injb ⟨ c′ , (_>>= f) ∘ ℋ⟦_⟧ ∘ k′ ⟩)
          ≡⟨ cong (λ ○ → impure (injb ⟨ c′ , ○ ⟩)) (extensionality λ x → catch-throw-lemma (k′ x)) ⟩  
            impure (injb ⟨ c′ , k′ ⟩) 
          ≡⟨ (cong impure (sym $ proj-injʳ _ _ eq)) ⟩
            impure ⟨ c , k ⟩
          QED
          
          where
            f = maybe′ pure (abort >>= pure)
            

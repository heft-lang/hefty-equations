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

open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open import Function
open import Data.Vec hiding ([_])
open import Relation.Unary hiding (Empty ; _⊆_)

module Effect.Instance.Catch.Elaboration where

open Connectives

CatchElab : Elaboration Catch Abort
CatchElab .elab = necessary λ i → CatchElabAlg ⦃ i ⦄
  where
    CatchElabAlg : ⦃ Abort ≲ ε ⦄ → Algebra Catch (Free ε)
    CatchElabAlg     ⦃ i           ⦄ .α ⟪ `throw   , k , s ⟫ = abort
    CatchElabAlg {ε} ⦃ i@(ε' , σ') ⦄ .α ⟪ `catch A , k , s ⟫ = do
      v ← ♯ (handleAbort σ' (s (inj₁ tt)))
      maybe′ k (s (inj₂ tt) >>= k) v

      where
        instance inst : ε' ≲ ε
        inst = Abort , union-comm σ'


-- 
-- elab-respects-bind : ∀ c r s (k : A → Free Abort B) → CatchElab .elab .α ⟪ c , r , s ⟫ >>= k ≡ CatchElab .elab .α ⟪ c , (_>>= k) ∘ r , s ⟫
-- elab-respects-bind `throw r s k = {!!}
-- elab-respects-bind (`catch t) r s k = {!!}
--


-- 
-- record HandleSem (ε : Effect) (F : Set → Set) : Set where
--   field ℋ⟦_⟧ : ∀[ Free ε ⇒ F ]
-- 
-- open HandleSem ⦃...⦄
-- 
-- record ElabSem (η : Effectᴴ) (ε : Effect) : Set where
--   field ℰ⟦_⟧ : ∀[ Hefty η ⇒ Free ε ]
-- 
--   ℰ : ∀[ Hefty η ⇒ Free ε ]
--   ℰ = ℰ⟦_⟧
--     
-- 
-- open ElabSem ⦃...⦄
-- 
-- instance catchESem : ElabSem Catch Abort
-- catchESem = record { ℰ⟦_⟧ = elaborate CatchElab }
-- 
-- instance abortHSem : HandleSem Abort Maybe
-- abortHSem = record { ℋ⟦_⟧ = λ x → {!!}  }
--

ℰ⟦_⟧ : ⦃ Abort ≲ ε ⦄ → ∀[ Hefty Catch ⇒ Free ε ]  
ℰ⟦_⟧ ⦃ i ⦄ = fold-hefty pure (□⟨ CatchElab .elab ⟩ i) 


CatchElabCorrect : Correctᴴ CatchTheory AbortTheory CatchElab
CatchElabCorrect px {ε′ = ε′} ⦃ i ⦄ T′ sub {γ = k} = go px sub 
  where
    open ≈-Reasoning T′
    instance inst : proj₁ i ≲ ε′
    inst = _ , (union-comm $ proj₂ i)

    ℋ⟦_⟧ : ∀[ Free ε′ ⇒ Maybe ⊢ Free ε′ ]
    ℋ⟦_⟧ = ♯ ∘ handleAbort (proj₂ i)

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
      ≈⟪ ≡-to-≈ (cong (λ ○ → ○ >>= λ v → maybe′ pure (ℰ⟦ m ⟧ >>= pure) v) lemma) ⟫
        pure nothing >>= maybe′ pure (ℰ⟦ m ⟧ >>= pure)
      ≈⟪⟫ {- Definition of >>= and maybe′ -} 
        ℰ⟦ m ⟧ >>= pure 
      ≈⟪ ≡-to-≈ identity-fold-lemma ⟫ 
        ℰ⟦ m ⟧
      ∎
      where
        {- TODO: make this into a more general lemma? -} 
        lemma : ℋ⟦ abort ⟧ ≡ pure nothing 
        lemma = {!!} 

    {- catch-throw-2 -} 
    go (there (there (there (here refl)))) sub {γ = m} =
      begin
        ℰ⟦ catch m throw ⟧
      ≈⟪⟫
        ℋ⟦ ℰ⟦ m ⟧ ⟧ >>= maybe′ pure (ℰ⟦ throw ⟧ >>= pure) 
      ≈⟪ {!!} ⟫
        ℋ⟦ ℰ⟦ m ⟧ ⟧ >>= maybe′ pure (ℰ⟦ throw ⟧) 
      ≈⟪ {!!} ⟫ 
        ℰ⟦ m ⟧
      ∎

    go (there (there (there (there (here refl))))) sub = {!!}

-- CatchElabCorrect (there (there (there (here refl)))) {δ = A ∷ []} {m} = ? 

  
--   begin
--     ℰ⟦ catch m throw ⟧
--   ≈⟪⟫ {- Definition of `elabCatch` -} 
--     maybe′ pure (abort >>= pure) ℋ⟦ ℰ⟦ m ⟧ ⟧
--   ≈⟪ maybe-lemma just-case (nothing-case m) ⟫
--     ℰ⟦ m ⟧
--   ∎

--   where 
--     nothing-case : ∀ m → ℋ⟦ ℰ⟦ m ⟧ ⟧ ≡ nothing → (abort >>= pure) ≈ ℰ⟦ m ⟧
--     nothing-case m eq = ?
--     {-
--       begin
--         abort >>= pure
--       ≈⟪ ≈-eq′ bind-abort (here refl)  ⟫
--         abort
--       ≈⟪ ?  ⟫
--         ℰ⟦ m ⟧
--       ∎
--       wher
--     -} 

--     {- 
--     just-case : (x′ : A) → ℋ⟦ ℰ⟦ m ⟧ ⟧ ≡ just x′ → pure x′ ≈ ℰ⟦ m ⟧
--     just-case x′ eq =
--       begin
--         pure x′
--       ≈⟪ adequacy (sym $ extract-lemma _ eq) ⟫
--         ℰ⟦ m ⟧
--       ∎
--       where open Adequacy
--     -} 

-- CatchElabCorrect (there (there (there (there (here refl))))) {_ ∷ _ ∷ []} {m₁ , m₂ , k , m₃} =

--   begin
--     ℰ⟦ catch (catch m₁ m₂ >>= k) m₃ ⟧
--   ≈⟪⟫ {- definition of `ℰ⟦_⟧` -} 
--     maybe′ pure (ℰ⟦ m₃ ⟧ >>= pure) ℋ⟦ ℰ⟦ catch m₁ m₂ >>= k ⟧ ⟧
--   ≈⟪⟫ {- Definition of `ℰ⟦_⟧` -} 
--     maybe′ pure (ℰ⟦ m₃ ⟧ >>= pure) ℋ⟦ maybe′ (ℰ⟦_⟧ ∘ k) (ℰ⟦ m₂ >>= pure ⟧ >>= (ℰ⟦_⟧ ∘ k)) ℋ⟦ ℰ⟦ m₁ >>= pure ⟧ ⟧ ⟧
--   ≈⟪ ≡-to-≈
--      ( cong₂
--          ( λ ○₁ ○₂ → maybe′ pure ○₁ ℋ⟦ maybe′ (ℰ⟦_⟧ ∘ k) (ℰ⟦ ○₂ ⟧ >>= (ℰ⟦_⟧ ∘ k)) ℋ⟦ ℰ⟦ m₁ >>= pure ⟧ ⟧ ⟧ )
--          identity-fold-lemma
--          (>>=-unitᵣ m₂)
--      ) ⟫
--     maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ maybe′ (ℰ⟦_⟧ ∘ k) (ℰ⟦ m₂ ⟧ >>= (ℰ⟦_⟧ ∘ k)) ℋ⟦ ℰ⟦ m₁ >>= pure ⟧ ⟧ ⟧ 
--   ≈⟪ ≡-to-≈
--      ( cong
--        ( λ ○ → maybe′ pure ℰ⟦ m₃ ⟧
--                  ℋ⟦ maybe′ (ℰ⟦_⟧ ∘ k) (ℰ⟦ m₂ ⟧ >>= (ℰ⟦_⟧ ∘ k)) ℋ⟦ ℰ⟦ ○ ⟧ ⟧ ⟧
--        ) (>>=-unitᵣ m₁)
--      ) ⟫ 
--     maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ maybe′ (ℰ⟦_⟧ ∘ k) (ℰ⟦ m₂ ⟧ >>= (ℰ⟦_⟧ ∘ k)) ℋ⟦ ℰ⟦ m₁ ⟧ ⟧ ⟧
--   ≈⟪ catch-catch-lemma m₁ m₂ m₃ k ⟫
--     maybe′ pure (maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ ℰ⟦ m₂ >>= k ⟧ ⟧) ℋ⟦ ℰ⟦ m₁ >>= k ⟧ ⟧
--   ≈⟪ ≡-to-≈
--      ( cong
--        ( λ ○ → maybe′ pure ○ ℋ⟦ ℰ⟦ m₁ >>= k ⟧ ⟧ )
--        (sym identity-fold-lemma)
--      ) ⟫
--     maybe′ pure (maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ ℰ⟦ m₂ >>= k ⟧ ⟧ >>= pure) ℋ⟦ ℰ⟦ m₁ >>= k ⟧ ⟧ 
--   ≈⟪ ≡-to-≈
--      ( cong
--        ( λ ○ → maybe′ pure (maybe′ pure ○ ℋ⟦ ℰ⟦ m₂ >>= k ⟧ ⟧ >>= pure) ℋ⟦ ℰ⟦ m₁ >>= k ⟧ ⟧ )
--        (sym identity-fold-lemma)
--      ) ⟫
--     maybe′ pure (maybe′ pure (ℰ⟦ m₃ ⟧ >>= pure) ℋ⟦ ℰ⟦ m₂ >>= k ⟧ ⟧ >>= pure) ℋ⟦ ℰ⟦ m₁ >>= k ⟧ ⟧
--   ≈⟪⟫ {- Definition of `ℰ⟦_⟧` -} 
--     maybe′ pure (ℰ⟦ catch (m₂ >>= k) m₃ ⟧ >>= pure) ℋ⟦ ℰ⟦ m₁ >>= k ⟧ ⟧
--   ≈⟪⟫ {- Definition of `ℰ⟦_⟧` -} 
--     ℰ⟦ catch (m₁ >>= k) (catch (m₂ >>= k) m₃) ⟧
--   ∎

--   where
--     catch-catch-lemma :
--       ∀ m₁ m₂ m₃ k →  maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ maybe′ (ℰ ∘ k) (ℰ⟦ m₂ ⟧ >>= ℰ ∘ k) ℋ⟦ ℰ⟦ m₁ ⟧ ⟧ ⟧
--                     ≈ maybe′ pure (maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ ℰ⟦ m₂ >>= k ⟧ ⟧) ℋ⟦ ℰ⟦ m₁ >>= k ⟧ ⟧  
--     catch-catch-lemma m₁ m₂ m₃ k with ℋ⟦ ℰ⟦ m₁ ⟧ ⟧ | inspect (λ x → ℋ⟦ ℰ⟦ x ⟧ ⟧) m₁
--     catch-catch-lemma m₁ m₂ m₃ k | just x | ≡[ eq ]  = {!!}
    
--     catch-catch-lemma m₁ m₂ m₃ k | nothing | ≡[ eq ] =
--       begin
--         maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ ℰ⟦ m₂ ⟧ >>= ℰ ∘ k ⟧
--       ≈⟪ ≡-to-≈ (cong (λ ○ → maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ ○ ⟧) (sym $ bind-lemma m₂ k)) ⟫
--        maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ ℰ⟦ m₂ >>= k ⟧ ⟧
--       ≈⟪⟫
--         maybe′ pure (maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ ℰ⟦ m₂ >>= k ⟧ ⟧) ℋ⟦ abort ⟧ 
--       ≈⟪ ≡-to-≈ (cong (λ ○ → maybe′ pure (maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ ℰ⟦ m₂ >>= k ⟧ ⟧) ○) (handle-lemma (≈-sym elab₂-lemma))) ⟫
--         maybe′ pure (maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ ℰ⟦ m₂ >>= k ⟧ ⟧) ℋ⟦ ℰ⟦ m₁ ⟧ >>= ℰ ∘ k ⟧ 
--       ≈⟪ ≡-to-≈ (cong (λ ○ → maybe′ pure ((maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ ℰ⟦ m₂ >>= k ⟧ ⟧)) ℋ⟦ ○ ⟧ ) (sym $ bind-lemma m₁ k)) ⟫
--         maybe′ pure (maybe′ pure ℰ⟦ m₃ ⟧ ℋ⟦ ℰ⟦ m₂ >>= k ⟧ ⟧) ℋ⟦ ℰ⟦ m₁ >>= k ⟧ ⟧
--       ∎
--       where
--         open Adequacy

--         elab₁-lemma : ℰ⟦ m₁ ⟧ ≈ abort
--         elab₁-lemma = adequacy (extract-lemma _ eq)

--         elab₂-lemma : ℰ⟦ m₁ ⟧ >>= ℰ ∘ k ≈ abort
--         elab₂-lemma = begin
--           ℰ⟦ m₁ ⟧ >>= ℰ ∘ k
--             ≈⟪ ≈-bind elab₁-lemma (ℰ ∘ k) ⟫ 
--           abort >>= ℰ ∘ k 
--             ≈⟪ ≈-eq′ bind-abort (here refl) ⟫
--           abort
--           ∎

--         handle-lemma : ∀ {A : Set} {c₁ c₂ : Free Abort A} → c₁ ≈ c₂ → ℋ⟦ c₁ ⟧ ≡ ℋ⟦ c₂ ⟧
--         handle-lemma ≈-refl = refl
--         handle-lemma (≈-sym eq) = sym $ handle-lemma eq
--         handle-lemma (≈-trans eq₁ eq₂) = trans (handle-lemma eq₁) (handle-lemma eq₂)
--         handle-lemma (≈-cong `abort p₁ p₂ eq) = refl 
--         handle-lemma (≈-eq eq (here refl) (_ ∷ _ ∷ []) γ) = refl
--         handle-lemma (≈-bind eq k) with handle-lemma eq
--         ... | r = {!!}

--         -- This suggests elaborations are functors? 
--         bind-lemma : {A B : Set} (m : Hefty Catch A) (k : A → Hefty Catch B) → ℰ⟦ m >>= k ⟧ ≡ ℰ⟦ m ⟧ >>= ℰ ∘ k
--         bind-lemma (pure x)               k = refl
--         bind-lemma (impure ⟪ c , r , s ⟫) k =
--           ≡-begin
--             ℰ⟦ impure ⟪ c , r , s ⟫ >>= k ⟧
--           ≡⟨⟩
--             ℰ⟦ impure ⟪ c , rec-hefty k (λ where .α → impure) ∘ r , rec-hefty pure (λ where .α → impure) ∘ s ⟫ ⟧
--           ≡⟨ cong (λ ○ → ℰ⟦ impure ⟪ c , rec-hefty k (λ where .α → impure) ∘ r , ○ ⟫ ⟧) (extensionality $ rec-identity-lemma ∘ s) ⟩
--             ℰ⟦ impure ⟪ c , rec-hefty k (λ where .α → impure) ∘ r , s ⟫ ⟧
--           ≡⟨⟩
--             {!CatchElab .elab α ⟪ ? , ? , ? ⟫!} 
--           ≡⟨ {!!} ⟩
--             CatchElab .elab .α ⟪ c , ℰ ∘ r , ℰ ∘ s ⟫ >>= ℰ ∘ k 
--           ≡⟨⟩ 
--             ℰ⟦ impure ⟪ c , r , s ⟫ ⟧ >>= ℰ ∘ k
--           ≡-∎

--           where
--             open ≡-Reasoning renaming (begin_ to ≡-begin_ ; _∎ to _≡-∎)
            
--             rec-identity-lemma : ∀ {η} {A} (m : Hefty η A) → rec-hefty pure (λ where .α → impure) m ≡ m
--             rec-identity-lemma (pure _)               = refl
--             rec-identity-lemma (impure ⟪ c , r , s ⟫) =
--               cong₂ (λ ○₁ ○₂ → impure ⟪ c , ○₁ , ○₂ ⟫)
--                 (extensionality $ rec-identity-lemma ∘ r)
--                 (extensionality $ rec-identity-lemma ∘ s)

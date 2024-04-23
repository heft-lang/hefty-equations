{-# OPTIONS --type-in-type --without-K #-}

open import Core.Functor
open import Core.Functor.Monad
open import Core.Ternary
open import Core.Logic

open import Core.MonotonePredicate 
open import Core.Signature
open import Core.Container
open import Core.Extensionality

open import Effect.Base
open import Effect.Syntax.Free
open import Effect.Syntax.Hefty

open import Effect.Handle
open import Effect.Elaborate

open import Effect.Theory.FirstOrder
open import Effect.Theory.HigherOrder

open import Effect.Relation.Binary.FirstOrderInclusion
open import Effect.Relation.Binary.HigherOrderInclusion
open import Effect.Relation.Ternary.FirstOrderSeparation
open import Effect.Relation.Ternary.HigherOrderSeparation

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

module Effect.Instance.LocalReader.Elaboration (R : Set) where

open import Effect.Instance.Reader.Syntax R
import Effect.Instance.Reader.Theory R as RT
open import Effect.Instance.Reader.Handler R

open import Effect.Instance.LocalReader.Syntax R
open import Effect.Instance.LocalReader.Theory R



open Handler ReaderHandler

coherence : ⦃ _ : Reader ≲ ε ⦄ → (m : Free ε A) (k : A → Free ε B) → ℋ⟦ m >>= k ⟧ ≡ ℋ⟦ m ⟧ >>= ℋ⟪ k ⟫
coherence {ε = ε} ⦃ i ⦄ m k =
  begin
    ℋ⟦ m >>= k ⟧
  ≡⟨⟩ 
    ♯ ∘ handle (i .proj₂) (m >>= k)
  ≡⟨ cong (♯ ∘_) (Properties.coherent (i .proj₂) m k) ⟩ 
    ♯ ∘ (handle (i .proj₂) m >>= (λ x → handle (i .proj₂) (k x))) 
  ≡⟨ extensionality (λ r → ♯-coherent (handle (i .proj₂) m r) λ x → handle (i .proj₂) (k x) r) ⟩
    ♯ ∘ handle (i .proj₂) m >>= (λ x → ♯ ∘ handle (i .proj₂) (k x)) 
  ≡⟨⟩ 
    ℋ⟦ m ⟧ >>= ℋ⟪ k ⟫
  ∎
  where
    open ≡-Reasoning
    instance inst : proj₁ i ≲ ε
    inst = Reader , (union-comm $ i .proj₂)


-- TODO: we can (and should) prove this as a general lemma for all handlers 
handle-merge : ⦃ _ : Reader ≲ ε ⦄ → (m : Free ε A) → (r r′ : R) → ℋ⟦ ℋ⟦ m ⟧ r ⟧ r′ ≡ ℋ⟦ m ⟧ r
handle-merge ⦃ i ⦄ m r r′ =
  begin
    ℋ⟦ ℋ⟦ m ⟧ r ⟧ r′
  ≡⟨⟩
    ♯ (handle (i .proj₂) (♯ (handle (i .proj₂) m r)) r′)
  ≡⟨ cong ♯ (cong (_$ r′) $ handle-modular (handle (i .proj₂) m r) (i .proj₂)) ⟩ 
    ♯ ((⇑ handle (i .proj₂) m r) r′)
  ≡⟨⟩ 
    ♯ (handle (i .proj₂) m r >>= flip return r′)
  ≡⟨ cong ♯ (>>=-idʳ (handle (i .proj₂) m r)) ⟩ 
    ♯ (handle (i .proj₂) m r) 
  ≡⟨⟩
    ℋ⟦ m ⟧ r
  ∎
  where
    open ≡-Reasoning
    instance inst : proj₁ i ≲ _
    inst = Reader , union-comm (i .proj₂) 

ReaderElab : Elaboration (LocalReader) Reader
ReaderElab .Elaboration.elab = necessary λ i → readerElab ⦃ i ⦄
  where
    readerElab : ⦃ Reader ≲ ε ⦄ → Algebra (LocalReader ε) (Free ε)
    readerElab .α ⟪ `ask ,       k , s ⟫ = ask >>= k
    readerElab .α ⟪ `local _ f , k , s ⟫ = do
      r ← ask 
      v ← ℋ⟦ s tt ⟧ (f r)
      k v

ReaderElab .Elaboration.commutes {f = f} ⟪ `ask , k , s ⟫ ⦃ i ⦄ =
  begin
    elab ⟪ `ask , fmap f ∘ k , s ⟫
  ≡⟨⟩ 
    ask >>= fmap f ∘ k 
  ≡⟨ (sym $ fmap->>= f ask k ) ⟩
    fmap f (ask >>= k) 
  ≡⟨⟩ 
    fmap f (elab ⟪ (`ask , k , s) ⟫)
  ∎
  where
    open ≡-Reasoning
    elab = (□⟨ Elaboration.elab ReaderElab ⟩ i) .α
ReaderElab .Elaboration.commutes {f = f} ⟪ `local t g , k , s ⟫ ⦃ i ⦄ =
  begin
    elab ⟪ `local t g , fmap f ∘ k , s ⟫
  ≡⟨⟩
    (ask >>= λ r → ℋ⟦ s tt ⟧ (g r) >>= fmap f ∘ k)
  ≡⟨ cong (ask >>=_) (extensionality λ r → sym $ fmap->>= f (ℋ⟦ s tt ⟧ (g r)) k) ⟩ 
    ask >>= (λ r → fmap f (ℋ⟦ s tt ⟧ (g r) >>= k)) 
  ≡⟨ sym (fmap->>= f ask (λ r → ℋ⟦ s tt ⟧ (g r) >>= k)) ⟩
    fmap f (ask >>= λ r → ℋ⟦ s tt ⟧ (g r) >>= k) 
  ≡⟨⟩ 
    fmap f (elab ⟪ `local t g , k , s ⟫)
  ∎
  where
    open ≡-Reasoning
    elab = (□⟨ Elaboration.elab ReaderElab ⟩ i) .α

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

instance refl-inst : ε ≲ ε
refl-inst = ≲-refl 

ReaderElabCorrect : Correctᴴ LocalReaderTheory RT.ReaderTheory ReaderElab

ReaderElabCorrect e′ (zero , refl) {γ = m} = 
  begin
    ℰ⟦ askl >> m ⟧
  ≈⟪ ≡-to-≈ $ elab-∘′ askl (λ _ → m) ⟫
    ℰ⟦ askl ⟧ >> ℰ⟦ m ⟧
  ≈⟪ >>=-resp-≈ˡ ℰ⟪ (λ _ → m) ⟫ (≡-to-≈ (use-elab-def _)) ⟫
    (ask >>= pure) >> ℰ⟦ m ⟧ 
  ≈⟪ >>=-resp-≈ˡ _ (>>=-idʳ-≈ ask ) ⟫
    ask >> ℰ⟦ m ⟧ 
  ≈⟪ ≈-eq′ (nec RT.ask-query) (zero , refl) ⟫
    ℰ⟦ m ⟧
  ∎
  where
    open ≈-Reasoning _
    open Elaboration e′
ReaderElabCorrect e′ (suc zero , refl) {γ = f , x} = 
  begin
    ℰ⟦ local f (return x) ⟧
  ≈⟪ ≡-to-≈ (use-elab-def _) ⟫ 
    (ask >>= λ r → ℋ⟦ return x ⟧ (f r))
  ≈⟪⟫
    ask >> return x
  ≈⟪ ≈-eq′ (nec RT.ask-query) (zero , refl) ⟫
    return x
  ∎
  where
    open ≈-Reasoning _
    open Elaboration e′
ReaderElabCorrect e′ (suc (suc zero) , refl) {γ = k} =
  begin 
    ℰ⟦ askl >>= (λ r → askl >>= k r) ⟧
  ≈⟪ ≡-to-≈ $ elab-∘′ askl (λ r → askl >>= k r) ⟫
    ℰ⟦ askl ⟧ >>= ℰ⟪ (λ r → askl >>= k r) ⟫ 
  ≈⟪ >>=-resp-≈ˡ _ (≡-to-≈ (use-elab-def _)) ⟫
    (ask >>= pure) >>= ℰ⟪ (λ r → askl >>= k r) ⟫ 
  ≈⟪ >>=-resp-≈ˡ _ (>>=-idʳ-≈ ask) ⟫ 
    ask >>= ℰ⟪ (λ r → askl >>= k r) ⟫ 
  ≈⟪ >>=-resp-≈ʳ ask (≡-to-≈ ∘ elab-∘′ askl ∘ k) ⟫
    ask >>= (λ r → ℰ⟦ askl ⟧ >>= ℰ⟪ k r ⟫)
  ≈⟪ >>=-resp-≈ʳ ask (λ r → >>=-resp-≈ˡ ℰ⟪ k r ⟫ (≡-to-≈ (use-elab-def _))) ⟫ 
    ask >>= (λ r → (ask >>= pure) >>= ℰ⟪ k r ⟫)
  ≈⟪ >>=-resp-≈ʳ ask (λ r → >>=-resp-≈ˡ ℰ⟪ k r ⟫ (>>=-idʳ-≈ ask)) ⟫ 
    ask >>= (λ z → ask >>= ℰ⟪ k z ⟫) 
  ≈⟪ ≈-eq′ (nec RT.ask-ask) (suc zero , refl) ⟫
    ask >>= (λ r → ℰ⟦ k r r ⟧) 
  ≈⟪ >>=-resp-≈ˡ (λ r → ℰ⟦ k r r ⟧) (≈-sym $ >>=-idʳ-≈ ask) ⟫
    (ask >>= pure) >>= (λ r → ℰ⟦ k r r ⟧)
  ≈⟪ >>=-resp-≈ˡ (λ r → ℰ⟦ k r r ⟧) ((≡-to-≈ (sym $ use-elab-def _))) ⟫
    (ℰ⟦ askl ⟧ >>= λ r → ℰ⟦ k r r ⟧) 
  ≈⟪ ≈-sym (≡-to-≈ (elab-∘′ askl (λ r → k r r))) ⟫ 
    ℰ⟦ askl >>= (λ r → k r r) ⟧ 
  ∎
  where
    open ≈-Reasoning _
    open Elaboration e′
ReaderElabCorrect e′ (suc (suc (suc zero)) , refl) {γ = m , k} =
  begin
    ℰ⟦ m >>= (λ x → askl >>= k x) ⟧
  ≈⟪ ≡-to-≈ (elab-∘′ m _) ⟫
    ℰ⟦ m ⟧ >>= (λ x → ℰ⟦ askl >>= k x ⟧)
  ≈⟪ >>=-resp-≈ʳ ℰ⟦ m ⟧ (λ x → ≡-to-≈ (elab-∘′ askl (k x))) ⟫ 
    ℰ⟦ m ⟧ >>= (λ x → ℰ⟦ askl ⟧ >>= ℰ⟪ k x ⟫)
  ≈⟪ >>=-resp-≈ʳ ℰ⟦ m ⟧ (λ x → >>=-resp-≈ˡ ℰ⟪ k x ⟫ (≈-trans (≡-to-≈ $ use-elab-def _) (>>=-idʳ-≈ ask))) ⟫
    ℰ⟦ m ⟧ >>= (λ x → ask >>= ℰ⟪ k x ⟫)
  ≈⟪ ≈-eq′ (nec RT.ask-bind) ((suc (suc zero)) , refl) {γ = ℰ⟦ m ⟧ , _} ⟫
    ask >>= (λ r → ℰ⟦ m ⟧ >>= λ x → ℰ⟦ k x r ⟧ )
  ≈⟪ >>=-resp-≈ˡ _ (≈-sym (≈-trans (≡-to-≈ $ use-elab-def _) (>>=-idʳ-≈ ask))) ⟫ 
    ℰ⟦ askl ⟧ >>= ((λ r → ℰ⟦ m ⟧ >>= λ x → ℰ⟦ k x r ⟧ )) 
  ≈⟪ >>=-resp-≈ʳ ℰ⟦ askl ⟧ (λ r → ≈-sym $ ≡-to-≈ $ elab-∘′ m λ x → k x r) ⟫
    ℰ⟦ askl ⟧ >>= (λ r → ℰ⟦ m >>= (λ x → k x r) ⟧) 
  ≈⟪ ≈-sym (≡-to-≈ (elab-∘′ askl _)) ⟫ 
    ℰ⟦ (askl >>= λ r → m >>= λ x → k x r) ⟧
  ∎
  where
    open ≈-Reasoning _
    open Elaboration e′
ReaderElabCorrect e′ (suc (suc (suc (suc zero))) , refl) {γ = m , k , f} =
  begin
    ℰ⟦ local f (m >>= k) ⟧
  ≈⟪ ≡-to-≈ (use-elab-def _) ⟫
    ask >>= (λ r → ℋ⟦ ℰ⟦ m >>= k ⟧ ⟧ (f r) >>= pure) 
  ≈⟪ >>=-resp-≈ʳ ask (λ r → >>=-idʳ-≈ _) ⟫
    ask >>= (λ r → ℋ⟦ ℰ⟦ m >>= k ⟧ ⟧ (f r))
  ≈⟪ >>=-resp-≈ʳ ask (λ r → ≡-to-≈ (cong (λ ○ → ℋ⟦ ○ ⟧ (f r)) (elab-∘′ m k))) ⟫
    ask >>= (λ r → ℋ⟦ (ℰ⟦ m ⟧ >>= ℰ⟪ k ⟫) ⟧ (f r))  
  ≈⟪ >>=-resp-≈ʳ ask (λ r → ≡-to-≈ $ cong (_$ (f r)) (coherence ℰ⟦ m ⟧ ℰ⟪ k ⟫)) ⟫ 
    ask >>= (λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r) >>= λ x → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r))
  ≈⟪ ≈-sym (≈-eq′ (nec RT.ask-ask) (suc zero , refl)) ⟫ 
    (ask >>= λ r → ask >>= λ r′ → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r) >>= λ x → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r′)) 
  ≈⟪ >>=-resp-≈ʳ ask (λ r → ≈-sym $ ≈-eq′ (nec RT.ask-bind) (suc (suc zero) , refl) {γ = (ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r)) , _}) ⟫
    (ask >>= λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r) >>= λ x → ask >>= λ r′ → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r′))
  ≈⟪ ≈-sym (>>=-assoc-≈ _ _ ask) ⟫
    (ask >>= λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r)) >>= (λ x → ask >>= λ r′ → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r′)) 
  ≈⟪ (>>=-resp-≈ʳ (((ask >>= λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r)))) λ x → >>=-resp-≈ʳ ask λ r′ → ≈-sym $ >>=-idʳ-≈ (ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r′))) ⟫
    ((ask >>= λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r))) >>= (λ x → ask >>= λ r′ → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r′) >>= pure)
  ≈⟪ >>=-resp-≈ˡ ((λ x → ask >>= λ r′ → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r′) >>= pure)) (>>=-resp-≈ʳ ask (λ r → ≈-sym (>>=-idʳ-≈ _))) ⟫
    (ask >>= (λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r) >>= pure)) >>= (λ x → ask >>= λ r′ → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r′) >>= pure) 
  ≈⟪ >>=-resp-≈ʳ (ask >>= (λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r) >>= pure)) (λ x → ≈-sym (≡-to-≈ (use-elab-def _))) ⟫
    (ask >>= (λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r) >>= pure)) >>= ℰ⟪ local f ∘ k ⟫ 
  ≈⟪ >>=-resp-≈ˡ ℰ⟪ local f ∘ k ⟫ (≈-sym (≡-to-≈ (use-elab-def _))) ⟫ 
    ℰ⟦ local f m ⟧ >>= ℰ⟪ local f ∘ k ⟫
  ≈⟪ ≈-sym (≡-to-≈ (elab-∘′ (local f m) (local f ∘ k))) ⟫ 
    ℰ⟦ local f m >>= local f ∘ k ⟧
  ∎
  where
    open ≈-Reasoning _
    open Elaboration e′

ReaderElabCorrect e′ ⦃ ζ ⦄ (suc (suc (suc (suc (suc zero)))) , refl) {γ = f} = 
  begin
    ℰ⟦ local f askl ⟧
  ≈⟪ ≡-to-≈ (use-elab-def _) ⟫
    ask >>= (λ r → ℋ⟦ ℰ⟦ askl ⟧ ⟧ (f r) >>= pure)
  ≈⟪ >>=-resp-≈ʳ ask (λ r → >>=-idʳ-≈ _) ⟫
    ask >>= (λ r → ℋ⟦ ℰ⟦ askl ⟧ ⟧ (f r))
  ≈⟪ >>=-resp-≈ʳ ask (λ r → ≡-to-≈ (cong (λ ○ → ℋ⟦ ○ ⟧ (f r)) (use-elab-def _))) ⟫ 
    ask >>= (λ r → ℋ⟦ ask >>= pure ⟧ (f r))
  ≈⟪ >>=-resp-≈ʳ ask (λ r → ≡-to-≈ (cong (λ ○ → ○ (f r)) (coherence ask pure))) ⟫ 
    ask >>= (λ r → ℋ⟦ ask ⟧ (f r) >>= λ r′ → ℋ⟦ pure r′ ⟧ (f r))
  ≈⟪⟫ 
    ask >>= (λ r → ℋ⟦ ask ⟧ (f r) >>= pure)
  ≈⟪ >>=-resp-≈ʳ ask (λ r → ≡-to-≈ (Properties.handle-ask (ζ .≲-eff .proj₂) pure)) ⟫
    ask >>= pure ∘ f
  ≈⟪ >>=-resp-≈ˡ (pure ∘ f) (≈-sym (>>=-idʳ-≈ ask)) ⟫ 
    (ask >>= pure) >>= pure ∘ f 
  ≈⟪ >>=-resp-≈ˡ (pure ∘ f) (≈-sym (≡-to-≈ (use-elab-def _))) ⟫ 
    ℰ⟦ askl ⟧ >>= pure ∘ f 
  ≈⟪ ≈-sym (≡-to-≈ (elab-∘′ askl (return ∘ f))) ⟫ 
    ℰ⟦ askl >>= return ∘ f  ⟧
  ∎
  where
    open ≈-Reasoning _
    open Elaboration e′

ReaderElabCorrect e′ ⦃ ζ ⦄ (suc (suc (suc (suc (suc (suc zero))))) , refl) {γ = f , g , m} =
  begin
    ℰ⟦ local (f ∘ g) m ⟧
  ≈⟪ ≡-to-≈ (use-elab-def _) ⟫ 
    ask >>= (λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f (g r)) >>= pure)
  ≈⟪ >>=-resp-≈ʳ ask (λ r → >>=-resp-≈ˡ pure (≡-to-≈ (sym $ handle-merge ℰ⟦ m ⟧ (f (g r)) (g r)))) ⟫
    ask >>= (λ r → ℋ⟦ ℋ⟦ ℰ⟦ m ⟧ ⟧ (f (g r)) ⟧ (g r) >>= pure)
  ≈⟪ >>=-resp-≈ʳ ask (λ r → >>=-resp-≈ˡ pure (≈-sym (≡-to-≈ (Properties.handle-ask (ζ .≲-eff .proj₂) _)))) ⟫ 
    ask >>= (λ r → (ℋ⟦ ask ⟧ (g r) >>= λ r′ → ℋ⟦ ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r′) ⟧ (g r)) >>= pure)  
  ≈⟪ >>=-resp-≈ʳ ask
       (λ r → >>=-resp-≈ˡ pure
         (>>=-resp-≈ʳ (ℋ⟦ ask ⟧ (g r)) λ r′ →
           ≡-to-≈ (cong (λ ○ → ℋ⟦ ○ ⟧ (g r)) (sym $ >>=-idʳ (ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r′))))))
   ⟫ 
    ask >>= (λ r → (ℋ⟦ ask ⟧ (g r) >>= λ r′ → ℋ⟦ ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r′) >>= pure ⟧ (g r)) >>= pure) 
  ≈⟪ >>=-resp-≈ʳ ask (λ r → >>=-resp-≈ˡ pure (≈-sym (≡-to-≈ (cong (_$ (g r)) (coherence ask _))))) ⟫ 
    ask >>= (λ r → ℋ⟦ ask >>= (λ r′ → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r′) >>= pure) ⟧ (g r) >>= pure)
  ≈⟪ >>=-resp-≈ʳ ask (λ r → >>=-resp-≈ˡ pure (≡-to-≈ (cong (λ ○ → ℋ⟦ ○ ⟧ (g r) ) (sym $ use-elab-def _)))) ⟫
    ask >>= (λ r → ℋ⟦ ℰ⟦ local f m ⟧ ⟧ (g r) >>= pure)
  ≈⟪ ≈-sym (≡-to-≈ (use-elab-def _)) ⟫ 
    ℰ⟦ local g (local f m) ⟧
  ∎
  where
    open ≈-Reasoning _
    open Elaboration e′ 

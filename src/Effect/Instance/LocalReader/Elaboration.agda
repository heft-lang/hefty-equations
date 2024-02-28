{-# OPTIONS --type-in-type --without-K #-}

open import Core.Functor
open import Core.Functor.Monad

open import Core.MonotonePredicate 
open import Core.Signature
open import Core.Container
open import Core.Extensionality

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

open import Effect.Instance.Reader.Syntax
import Effect.Instance.Reader.Theory as RT
open import Effect.Instance.Reader.Handler

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

module Effect.Instance.LocalReader.Elaboration (R : Set) where

open Connectives

open import Effect.Instance.LocalReader.Syntax R
open import Effect.Instance.LocalReader.Theory R

open Handler (ReaderHandler R)

coherence : ⦃ _ : Reader R ≲ ε ⦄ → (m : Free ε A) (k : A → Free ε B) (r : R) → ℋ⟦ m >>= k ⟧ r ≡ ℋ⟦ m ⟧ r >>= λ x → ℋ⟦ k x ⟧ r
coherence {ε = ε} ⦃ i ⦄ m k r =
  begin
    ℋ⟦ m >>= k ⟧ r
  ≡⟨⟩
    ♯ ⦃ inst ⦄ (handle (i .proj₂) (m >>= k) r) 
  ≡⟨ cong (♯ ⦃ inst ⦄) (Properties.coherent (i .proj₂) m k r) ⟩
    ♯ ⦃ inst ⦄ (handle (i .proj₂) m r >>= λ x → handle (i .proj₂) (k x) r)  
  ≡⟨ ♯-coherent ⦃ inst ⦄ (handle (i .proj₂) m r) (λ x → handle (i .proj₂) (k x) r) ⟩
    ♯ ⦃ inst ⦄ (handle (i .proj₂) m r ) >>= (λ x → ♯ ⦃ inst ⦄ (handle (i .proj₂) (k x) r)) 
  ≡⟨⟩ 
    ℋ⟦ m ⟧ r >>= (λ x → ℋ⟦ k x ⟧ r)
  ∎

  where
    open ≡-Reasoning
    inst : proj₁ i ≲ ε
    inst = Reader R , (union-comm $ i .proj₂)

-- TODO: we can (and should) prove this as a general lemma for all handlers 
handle-merge : ⦃ _ : Reader R ≲ ε ⦄ → (m : Free ε A) → (r r′ : R) → ℋ⟦ ℋ⟦ m ⟧ r ⟧ r′ ≡ ℋ⟦ m ⟧ r
handle-merge ⦃ px ⦄ m r r′ =
  begin
    ℋ⟦ ℋ⟦ m ⟧ r ⟧ r′
  ≡⟨⟩
    ♯ʳ′ σ' (handle σ' r′ (♯ʳ′ σ' (handle σ' r m)))
  ≡⟨ cong (♯ʳ′ σ') (handle-modular (ReaderHandler R) (handle σ' r m) σ' r′) ⟩
    ♯ʳ′ σ' (fmap {F = Free (proj₁ px)} id (handle σ' r m)) 
  ≡⟨ cong (♯ʳ′ σ') (fmap-id {F = Free (proj₁ px)} (handle σ' r m)) ⟩
    ♯ʳ′ σ' (handle σ' r m) 
  ≡⟨⟩ 
   ℋ⟦ m ⟧ r
  ∎
  where
    open ≡-Reasoning 
    σ' = px .proj₂


ReaderElab : Elaboration (LocalReader) (Reader R)
ReaderElab .Elaboration.elab = necessary λ i → readerElab ⦃ i ⦄
  where
    readerElab : ⦃ Reader R ≲ ε ⦄ → Algebra (LocalReader ε) (Free ε)
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



ReaderElabCorrect : Correctᴴ LocalReaderTheory RT.ReaderTheory ReaderElab

-- ask-query
ReaderElabCorrect (here refl) {ε′} ⦃ i ⦄ T′ ζ {γ = m} =
  begin
    ℰ⟦ askl >> m ⟧
  ≈⟪⟫  
    ℰ⟦ impure ⟪ `ask , pure , (λ())  ⟫ >> m ⟧
  ≈⟪⟫
    ℰ⟦ impure ⟪ `ask , (λ x → pure x >> m) , (λ()) ⟫ ⟧
  ≈⟪⟫
    ask >>= (λ x → pure x >> ℰ⟦ m ⟧)
  ≈⟪ ≈-sym $ >>=-assoc-≈ pure (λ _ → ℰ⟦ m ⟧) ask ⟫ 
    (ask >>= pure) >> ℰ⟦ m ⟧ 
  ≈⟪ >>=-resp-≈ˡ (λ _ → ℰ⟦ m ⟧) (>>=-idʳ-≈ ask) ⟫
    ask >> ℰ⟦ m ⟧
  ≈⟪ ≈-eq′ (weaken i RT.ask-query) (ζ .sub (here refl)) ⟫
    ℰ⟦ m ⟧
  ∎
  where
    open ≈-Reasoning T′
    open Elaboration ReaderElab

-- local-return 
ReaderElabCorrect (there (here refl)) {ε′} ⦃ i ⦄ T′ ζ {γ = f , x} =
  begin
    ℰ⟦ local f (return x) ⟧
  ≈⟪⟫
    ask >>= (λ r → ℋ⟦ return x ⟧ (f r))
  ≈⟪⟫ 
    ask >> return x 
  ≈⟪ ≈-eq′ (weaken i RT.ask-query) (ζ .sub (here refl)) ⟫
    return x
  ∎
  where
    open ≈-Reasoning T′
    open Elaboration ReaderElab


-- ask-bind 
ReaderElabCorrect (there (there (here refl))) {ε′} ⦃ i ⦄ T′ ζ {γ = m , k} =
  begin
    ℰ⟦ m >>= (λ x → askl >>= λ r → k x r) ⟧
  ≈⟪ ≡-to-≈ $ elab-∘′ m (λ x → askl >>= λ r → k x r) ⟫
    ℰ⟦ m ⟧ >>= (λ x → ℰ⟦ (askl >>= λ r → k x r) ⟧)
  ≈⟪ >>=-resp-≈ʳ ℰ⟦ m ⟧ (λ x → ≡-to-≈ $ elab-∘′ askl (k x)) ⟫
    ℰ⟦ m ⟧ >>= (λ x → ℰ⟦ askl ⟧ >>= λ r → ℰ⟦ k x r ⟧ )
  ≈⟪⟫
    ℰ⟦ m ⟧ >>= (λ x → (ask >>= pure) >>= λ r → ℰ⟦ k x r ⟧)
  ≈⟪ >>=-resp-≈ʳ ℰ⟦ m ⟧ (λ x → >>=-resp-≈ˡ (λ r → ℰ⟦ k x r ⟧) ( >>=-idʳ-≈ ask)) ⟫ 
    ℰ⟦ m ⟧ >>= (λ x → ask >>= λ r → ℰ⟦ k x r ⟧)
  ≈⟪ ≈-eq′ (weaken i RT.ask-bind) (ζ .sub (there (there (here refl)))) {γ = ℰ⟦ m ⟧ , _}  ⟫
    ask >>= (λ r → ℰ⟦ m ⟧ >>= λ x → ℰ⟦ k x r ⟧) 
  ≈⟪ >>=-resp-≈ˡ (λ r → ℰ⟦ m ⟧ >>= λ x → ℰ⟦ k x r ⟧) (≈-sym $ >>=-idʳ-≈ ask) ⟫ 
    (ask >>= pure) >>= (λ r → ℰ⟦ m ⟧ >>= λ x → ℰ⟦ k x r ⟧) 
  ≈⟪⟫ 
    ℰ⟦ askl ⟧ >>= (λ r → ℰ⟦ m ⟧ >>= λ x → ℰ⟦ k x r ⟧ )  
  ≈⟪ >>=-resp-≈ʳ ℰ⟦ askl ⟧ (λ r → ≈-sym (≡-to-≈ (elab-∘′ m λ x → k x r))) ⟫ 
    ℰ⟦ askl ⟧ >>= (λ r → ℰ⟦ (m >>= λ x → k x r) ⟧) 
  ≈⟪ ≈-sym (≡-to-≈ (elab-∘′ askl λ r → m >>= λ x → k x r)) ⟫ 
    ℰ⟦ (askl >>= λ r → m >>= λ x → k x r) ⟧
  ∎
  where
    open ≈-Reasoning T′
    open Elaboration ReaderElab


-- local-bind 
ReaderElabCorrect (there (there (there (here refl)))) {ε′} ⦃ i ⦄ T′ ζ {γ = m , k , f} =
  begin
    ℰ⟦ local f (m >>= k) ⟧
  ≈⟪⟫
    ask >>= (λ r → ℋ⟦ ℰ⟦ m >>= k ⟧ ⟧ (f r) >>= pure)
  ≈⟪ >>=-resp-≈ʳ ask (λ r → >>=-idʳ-≈ (ℋ⟦ ℰ⟦ m >>= k ⟧ ⟧ (f r))) ⟫
    ask >>= (λ r → ℋ⟦ ℰ⟦ m >>= k ⟧ ⟧ (f r) ) 
  ≈⟪ >>=-resp-≈ʳ ask (λ r → ≡-to-≈ (cong (λ ○ → ℋ⟦ ○ ⟧ (f r)) (elab-∘′ m k))) ⟫
    ask >>= (λ r → ℋ⟦ ℰ⟦ m ⟧ >>= ℰ⟪ k ⟫ ⟧ (f r))
  ≈⟪ ≡-to-≈ (cong (λ ○ → ask >>= ○) (extensionality λ r → coherence ℰ⟦ m ⟧ ℰ⟪ k ⟫ (f r)) ) ⟫ 
    ask >>= (λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r) >>= λ x → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r))
  ≈⟪ ≈-sym $ ≈-eq′ (weaken i RT.ask-ask) (ζ .sub (there (here refl))) ⟫ 
    ask >>= (λ r → ask >>= λ r′ → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r) >>= λ x → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r′)) 
  ≈⟪ >>=-resp-≈ʳ ask (λ r → ≈-sym $ ≈-eq′ (weaken i RT.ask-bind) (ζ .sub (there (there (here refl)))) {γ = ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r) , _}) ⟫
    ask >>= (λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r) >>= λ x → ask >>= λ r → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r)) 
  ≈⟪ ≈-sym $ >>=-assoc-≈ (λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r)) (λ x → ask >>= λ r′ → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r′)) ask ⟫ 
    (ask >>= λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r)) >>= (λ x → ask >>= λ r′ → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r′)) 
  ≈⟪ >>=-resp-≈ʳ ((ask >>= λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r))) (λ x → >>=-resp-≈ʳ ask λ r → ≈-sym (>>=-idʳ-≈ (ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r)))) ⟫ 
    (ask >>= λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r)) >>= ((λ x → ask >>= λ r′ → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r′) >>= pure)) 
  ≈⟪ >>=-resp-≈ˡ ((λ x → ask >>= λ r → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r) >>= pure)) (>>=-resp-≈ʳ ask λ r → ≈-sym $ >>=-idʳ-≈ (ℋ⟦ ℰ⟦ m ⟧ ⟧ ((f r)))) ⟫ 
    ((ask >>= λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r) >>= pure)) >>= (λ x → ask >>= λ r′ → ℋ⟦ ℰ⟦ k x ⟧ ⟧ (f r′) >>= pure)
  ≈⟪⟫ 
    (ask >>= λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r) >>= pure) >>= (λ x → ℰ⟦ local f (k x) ⟧) 
  ≈⟪⟫ 
    ℰ⟦ local f m ⟧ >>= (λ x → ℰ⟦ local f (k x) ⟧) 
  ≈⟪ ≈-sym $ ≡-to-≈ (elab-∘′ (local f m) λ x → local f (k x)) ⟫
    ℰ⟦ local f m >>= (λ x → local f (k x)) ⟧
  ∎
  where
    open ≈-Reasoning T′
    open Elaboration ReaderElab

-- local-ask 
ReaderElabCorrect (there (there (there (there (here refl))))) {ε′} ⦃ i ⦄ T′ ζ {γ = f} =
  begin
    ℰ⟦ local f askl ⟧
  ≈⟪⟫
    ask >>= (λ r → ℋ⟦ ask >>= pure ⟧ (f r) >>= pure)
  ≈⟪ ≡-to-≈ (cong (λ ○ → ask >>= (○ >=> pure)) (extensionality λ r → coherence ask pure (f r))) ⟫ 
    (ask >>= λ r → (ℋ⟦ ask ⟧ (f r) >>= λ x → ℋ⟦ pure x ⟧ (f r)) >>= pure) 
  ≈⟪ >>=-resp-≈ʳ ask (λ r → >>=-idʳ-≈ ((ℋ⟦ ask ⟧ (f r) >>= λ x → ℋ⟦ pure x ⟧ (f r)))) ⟫ 
    ask >>= (λ r → (ℋ⟦ ask ⟧ (f r) >>= λ x → ℋ⟦ pure x ⟧ (f r)) )
  ≈⟪⟫
    ask >>= (λ r → ℋ⟦ ask ⟧ (f r) >>= return )
  ≈⟪ >>=-resp-≈ʳ ask (λ r → ≡-to-≈ (Properties.handle-ask (i .proj₂) return)) ⟫
    ask >>= return ∘ f 
  ≈⟪⟫ 
    ℰ⟦ askl >>= return ∘ f ⟧
  ∎
  where
    open ≈-Reasoning T′
    open Elaboration ReaderElab

-- local-local 
ReaderElabCorrect (there (there (there (there (there (here refl)))))) {ε′} ⦃ i ⦄ T′ ζ {γ = f , g , m} =
  begin
    ℰ⟦ local (f ∘ g) m ⟧
  ≈⟪⟫ 
    ask >>= (λ r → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f (g r)) >>= pure) 
  ≈⟪ >>=-resp-≈ʳ ask (λ r → >>=-resp-≈ˡ pure (≡-to-≈ (sym $ handle-merge ℰ⟦ m ⟧ (f (g r)) (g r)))) ⟫ 
    ask >>= (λ r → ℋ⟦ ℋ⟦ ℰ⟦ m ⟧ ⟧ (f (g r)) ⟧ (g r) >>= pure) 
  ≈⟪ >>=-resp-≈ʳ ask (λ r → >>=-resp-≈ˡ pure (≡-to-≈ (cong (λ ○ → ℋ⟦ ○ ⟧ (g r)) (sym $ >>=-idʳ (ℋ⟦ ℰ⟦ m ⟧ ⟧ (f (g r))) )))) ⟫ 
    ask >>= (λ r → ℋ⟦ ℋ⟦ ℰ⟦ m ⟧ ⟧ (f (g r)) >>= pure ⟧ (g r) >>= pure) 
  ≈⟪ >>=-resp-≈ʳ ask (λ r → >>=-resp-≈ˡ pure (≡-to-≈ (sym (Properties.handle-ask (i .proj₂) _)))) ⟫ 
    (ask >>= λ r → (ℋ⟦ ask ⟧ (g r) >>= (λ r′ → ℋ⟦ ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r′) >>= pure ⟧ (g r))) >>= pure)
  ≈⟪ ≡-to-≈ (cong (λ ○ → ask >>= (○ >=> pure)) (extensionality λ r → sym $ coherence ask (λ r′ → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r′) >>= pure) (g r))) ⟫ 
    ask >>= (λ r → ℋ⟦ (ask >>= λ r′ → ℋ⟦ ℰ⟦ m ⟧ ⟧ (f r′) >>= pure ) ⟧ (g r) >>= pure) 
  ≈⟪⟫ 
    ask >>= (λ r → ℋ⟦ ℰ⟦ local f m ⟧ ⟧ (g r) >>= pure)
  ≈⟪⟫ 
    ℰ⟦ local g (local f m) ⟧
  ∎
  where
    open ≈-Reasoning T′
    open Elaboration ReaderElab

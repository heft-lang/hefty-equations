{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Functor.Monad
open import Core.Functor.NaturalTransformation

open import Core.Container
open import Core.Extensionality

open import Data.Product
open import Data.Sum

open import Effect.Base
open import Effect.Handle
open import Effect.Separation
open import Effect.Inclusion
open import Effect.Logic
open import Effect.Syntax.Free 

open import Function

open import Effect.Theory.FirstOrder

open import Effect.Instance.Reader.Syntax
open import Effect.Instance.Reader.Theory

open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open import Relation.Unary

open import Core.MonotonePredicate Effect _≲_

module Effect.Instance.Reader.Handler where 

open Connectives hiding (_⟨_⟩_)

module _ where 

  instance readerT-functor : ∀ {R : Set} → Functor (const R ⇒ Free ε)
  readerT-functor = record
    { fmap    = λ f g r → fmap f (g r)
    ; fmap-id = extensionality
        λ g → cong (λ ○ → λ r → ○ (g r)) $ fmap-id {F = Free _ }
    ; fmap-∘  = λ f g → extensionality
        λ h → cong (λ ○ → λ r → ○ (h r)) (fmap-∘ {F = Free _ } f g)
    }

  instance readerT-monad : ∀ {ε R} → Monad (const R ⇒ id ⊢ Free ε)
  readerT-monad = record
    { F-functor      = readerT-functor 
    ; return         = λ x r → pure x
    ; _∗             = λ f g r → g r >>= λ x → f x r
    ; >>=-idˡ        = λ _ _ → refl
    ; >>=-idʳ        =
        λ f → extensionality λ r → >>=-idʳ (f r)
    ; >>=-assoc      =
        λ k₁ k₂ m
          → extensionality λ r → >>=-assoc (flip k₁ r) (flip k₂ r) (m r)
    ; return-natural =
        λ where
          .commute {f = f} x
            → extensionality λ r → return-natural .commute {f = f} x
    } 
  
  ReaderHandler : ∀ R → Handler (Reader R) R id
  Handler.F-functor (ReaderHandler _) = id-functor
  Handler.M-monad   (ReaderHandler _) = readerT-monad 

  Handler.hdl (ReaderHandler _) .αᶜ ⟨ `ask , k ⟩ r = k r r

  Handler.M-apply     (ReaderHandler _)                = refl
  Handler.hdl-commute (ReaderHandler _) f ⟨ `ask , k ⟩ = refl
  

open Handler

handleReader : ∀ {R} → Reader R ∙ ε ≈ ε′ → Free ε′ A → R → Free ε A 
handleReader σ t r = handle (ReaderHandler _) σ t r

module Properties where

  modular : ∀ {R} → Modular (ReaderHandler R)
  modular = handle-modular (ReaderHandler _)
  
  correct : ∀ {R} → Correct ReaderTheory (ReaderHandler R)
  correct (here refl)                                                              = refl
  correct (there (here refl))                                                      = refl 
  correct (there (there (here refl))) {δ = δ} {γ = pure x , k} {k′}                = refl
  correct (there (there (here refl))) {δ = δ} {γ = impure ⟨ `ask , k′′ ⟩ , k} {k′} = extensionality $ λ r → 
    begin
      handle' (impure ⟨ `ask , k′′ ⟩ >>= (λ x → ask >>= λ r → k x r)) r
    ≡⟨⟩
      handle' (impure ⟨ `ask , (λ v → k′′ v >>= λ x → ask >>= λ r → k x r) ⟩) r
    ≡⟨⟩
      handle' (k′′ r >>= λ x → ask >>= λ r → k x r) r
    ≡⟨ handle-cong (k′′ r) (λ x → ask >>= λ r → k x r) (λ x → k x r) r refl ⟩
      handle' (k′′ r >>= (λ x → k x r)) r 
    ≡⟨⟩ 
      handle' (impure ⟨ `ask , (λ v → k′′ v >>= λ x → k x r) ⟩) r 
    ≡⟨⟩ 
      handle' (ask >>= λ r → impure ⟨ `ask , k′′ ⟩ >>= λ x → k x r) r
    ∎
    where
      open ≡-Reasoning 
      instance inst : {R : Set} → Reader R ≲ Reader R
      inst = ≲-refl

      handle' = fold-free k′ (ReaderHandler _ .hdl) 

      handle-cong :
        ∀ (m : Free (Reader _) A) (k₁ k₂ : A → Free _ _) r
        → (∀ {x} → handle' (k₁ x) r ≡ handle' (k₂ x) r)
        → handle' (m >>= k₁) r ≡ handle' (m >>= k₂) r 
      handle-cong (pure x)              k₁ k₂ r eq = eq {x}
      handle-cong (impure ⟨ `ask , k ⟩) k₁ k₂ r eq =
        begin
          handle' (impure ⟨ `ask , k ⟩ >>= k₁) r
        ≡⟨⟩ 
          handle' (impure ⟨ `ask , (k >=> k₁) ⟩) r
        ≡⟨⟩
          handle' (k r >>= k₁) r 
        ≡⟨ handle-cong (k r) k₁ k₂ r eq ⟩
          handle' (k r >>= k₂) r 
        ≡⟨⟩ 
          handle' (impure ⟨ `ask , (k >=> k₂) ⟩) r 
        ≡⟨⟩ 
          handle' (impure ⟨ `ask , k ⟩ >>= k₂) r
        ∎

  handle-ask : ∀ {R} {r} (σ : Reader R ∙ ε′ ≈ ε) → (k : R → Free ε A) → ♯ ⦃ _ , union-comm σ ⦄ (handleReader σ (ask ⦃ _ , σ ⦄) r) >>= k ≡ k r   
  handle-ask {ε′ = ε′} {ε = ε} {r = r} σ k =
    begin
      ♯ (handleReader σ ask r) >>= k
    ≡⟨⟩ 
      ♯ (handleReader σ (impure (inj ⟨ (`ask , pure) ⟩)) r) >>= k
    ≡⟨⟩
      ♯ (handle′ (ReaderHandler _) (fold-free pure (λ where .αᶜ → impure ∘ proj σ) (impure (inj ⟨ `ask , pure ⟩))) r ) >>= k
    ≡⟨⟩
      ♯ (handle′ (ReaderHandler _) (impure (proj σ (fmap (reorder σ) (inj ⟨ (`ask , pure) ⟩)))) r) >>= k
    ≡⟨ cong (λ ○ → ♯ (handle′ (ReaderHandler _) (impure (proj σ ○)) r) >>= k) (sym (inj-natural .commute {f = reorder σ} ⟨ (`ask , pure) ⟩)) ⟩ 
      ♯ (handle′ (ReaderHandler _) (impure (proj σ (inj ( ⟨ `ask , reorder σ ∘ pure ⟩)))) r) >>= k
    ≡⟨ cong (λ ○ → ♯ (handle′ (ReaderHandler _) (impure ○) r) >>= k) (σ .union .equivalence _ .inverse .proj₂ _) ⟩ 
      ♯ (handle′ (ReaderHandler _) (impure (injˡ {C₁ = Reader _} ε′ ( ⟨ `ask , reorder σ ∘ pure ⟩))) r) >>= k
    ≡⟨⟩
      k r
    ∎
    where
      open Union
      open Inverse 
      open ≡-Reasoning
      instance inst : Reader _ ≲ _
      inst = _ , σ
      instance inst′ : ε′ ≲ ε
      inst′ = _ , union-comm σ

  open ≡-Reasoning 

  coherent′ : ∀ {R} → Coherent′ (ReaderHandler R)
  coherent′ (pure x)                    k = refl
  coherent′ (impure ⟨ inj₁ `ask , k′ ⟩) k = extensionality λ r →
    begin
      handle′ (ReaderHandler _) (impure ⟨ inj₁ `ask , (k′ >=> k) ⟩) r
    ≡⟨⟩
      handle′ (ReaderHandler _) (k′ r >>= k) r 
    ≡⟨ (cong (_$ r) $ coherent′ (k′ r) k) ⟩
      handle′ (ReaderHandler _) (k′ r) r >>= flip (handle′ (ReaderHandler _)) r ∘ k 
    ≡⟨⟩ 
      handle′ (ReaderHandler _) (impure ⟨ inj₁ `ask , k′ ⟩) r >>= flip (handle′ (ReaderHandler _)) r ∘ k
    ∎ 
  coherent′ (impure ⟨ inj₂ c    , k′ ⟩) k = extensionality λ r → 
    begin
      h (impure ⟨ inj₂ c , k′ >=> k ⟩) r
    ≡⟨⟩
      impure ⟨ c , flip h r ∘ (k′ >=> k) ⟩ 
    ≡⟨ cong (λ ○ → impure ⟨ c , ○ ⟩) (extensionality λ x → cong (_$ r) $ coherent′ (k′ x) k) ⟩ 
      impure ⟨ c , flip h r ∘  k′ ⟩ >>= flip h r ∘ k 
    ≡⟨⟩ 
      h (impure ⟨ inj₂ c , k′ ⟩) r >>= flip h r ∘ k
    ∎
    where
      h = handle′ (ReaderHandler _)

  coherent : ∀ {R} → Coherent (ReaderHandler R)
  coherent = reordering-preserves-coherence (ReaderHandler _) coherent′ 

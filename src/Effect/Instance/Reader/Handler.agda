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

open import Core.MonotonePredicate Effect _≲_

module Effect.Instance.Reader.Handler where 

open Connectives hiding (_⟨_⟩_)

ReaderHandler : ∀ R → Handler (Reader R) R id
ReaderHandler _ = record
  { gen = const
  ; hdl = record { αᶜ = λ where ⟨ `ask , k ⟩ r → k r r }
  }

handleReader : ∀ {R} → Reader R ∙ ε ≈ ε′ → Free ε′ A → R → Free ε A 
handleReader σ t r = handle (ReaderHandler _) σ r t


module Properties where

  modular : ∀ {R} → Modular (ReaderHandler R)
  modular = handle-modular (ReaderHandler _)
  
  correct : ∀ {R} → Correct ReaderTheory (ReaderHandler R)
  correct (here refl)                                                 = refl
  correct (there (here refl))                                         = refl 
  correct (there (there (here refl))) {δ = δ} {γ = pure x , k} {k′}   = refl
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
      ♯ (handle′ (ReaderHandler _) r (fold-free pure (λ where .αᶜ → impure ∘ proj σ) (impure (inj ⟨ `ask , pure ⟩))) ) >>= k
    ≡⟨⟩
      ♯ (handle′ (ReaderHandler _) r (impure (proj σ (fmap (separate σ) (inj ⟨ (`ask , pure) ⟩))))) >>= k
    ≡⟨ cong (λ ○ → ♯ (handle′ (ReaderHandler _) r (impure (proj σ ○))) >>= k) (sym (inj-natural .commute {f = separate σ} ⟨ (`ask , pure) ⟩)) ⟩ 
      ♯ (handle′ (ReaderHandler _) r (impure (proj σ (inj ( ⟨ `ask , separate σ ∘ pure ⟩))))) >>= k
    ≡⟨ cong (λ ○ → ♯ (handle′ (ReaderHandler _) r (impure ○)) >>= k) (σ .union .equivalence _ .inverse .proj₂ _) ⟩ 
      ♯ (handle′ (ReaderHandler _) r (impure (injˡ {C₁ = Reader _} ε′ ( ⟨ `ask , separate σ ∘ pure ⟩)))) >>= k
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

  coherent′ : ∀ {R} → Coherent′ (ReaderHandler R)
  coherent′ (pure x)                    k r = refl
  coherent′ (impure ⟨ inj₁ `ask , k′ ⟩) k r = coherent′ (k′ r) k r
  coherent′ (impure ⟨ inj₂ c    , k′ ⟩) k r =
    begin
      handle′ (ReaderHandler _) r (impure ⟨ inj₂ c , (k′ >=> k) ⟩)
    ≡⟨ handle-modular′′ (ReaderHandler _) c (k′ >=> k) r ⟩
      impure ⟨ c , handle′ (ReaderHandler _) r ∘ (k′ >=> k) ⟩
    ≡⟨ cong (λ ○ → impure ⟨ c , ○ ⟩) (extensionality λ x → coherent′ (k′ x) k r) ⟩
      impure ⟨ c , (λ z → (handle′ (ReaderHandler _) r (k′ z)) >>= (handle′ (ReaderHandler _) r ∘ k)) ⟩ 
    ≡⟨⟩ 
      handle′ (ReaderHandler _) r (impure ⟨ inj₂ c , k′ ⟩) >>= handle′ (ReaderHandler _) r ∘ k
    ∎
    where open ≡-Reasoning 

  coherent : ∀ {R} → Coherent (ReaderHandler R)
  coherent = sep-coherent (ReaderHandler _) coherent′

{-# OPTIONS --without-K #-} 

open import Core.Functor
open import Core.Functor.Monad
open import Core.Functor.NaturalTransformation

open import Core.Container
open import Core.Extensionality
open import Core.Ternary
open import Core.Logic

open import Effect.Base
open import Effect.Handle
open import Effect.Syntax.Free

open import Effect.Relation.Binary.FirstOrderInclusion
open import Effect.Relation.Ternary.FirstOrderSeparation

open import Data.Unit
open import Data.Maybe hiding (_>>=_)
open import Data.Product
open import Data.Vec
open import Data.Sum
open import Data.Empty

open import Function 

open import Effect.Theory.FirstOrder

open import Effect.Instance.Abort.Syntax
open import Effect.Instance.Abort.Theory

open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open import Relation.Unary

open import Level

open import Core.MonotonePredicate Effect _≲_

module Effect.Instance.Abort.Handler where

instance maybe-functor : Functor {a = 0ℓ} Maybe
maybe-functor = record
  { fmap    = λ f → maybe (just ∘ f) nothing
  ; fmap-id = extensionality (maybe (λ _ → refl) refl)
  ; fmap-∘  = λ f g → extensionality (maybe (λ _ → refl) refl)
  } 

⊤-functor : Functor F → Functor (const ⊤ ⇒ F)
⊤-functor ff = record
  { fmap    = λ where f x tt → fmap ⦃ ff ⦄ f (x tt)
  ; fmap-id = pfext _ _
      λ m → cong (λ where ○ tt → ○ (m tt)) $ fmap-id ⦃ ff ⦄ 
  ; fmap-∘  = λ f g → pfext _ _
      λ m → cong (λ where ○ tt → ○ (m tt)) (fmap-∘ ⦃ ff ⦄ f g)
  } 

instance abortT-functor : Functor (const ⊤ ⇒ Maybe ⊢ Free ε)
abortT-functor = ⊤-functor (∘-functor maybe-functor free-functor) 

open ≡-Reasoning

instance readerT-monad : Monad (const ⊤ ⇒ Maybe ⊢ Free ε)
readerT-monad = record
  { return         = λ where x tt → pure (just x)
  ; _∗             = λ where f m tt → m tt >>= maybe′ (flip f tt) (pure nothing)
  ; >>=-idˡ        = λ x k → refl
  ; >>=-idʳ        = λ m → extensionality λ where
      tt → begin
             m tt >>= maybe′ (pure ∘ just) (pure nothing)
           ≡⟨ cong (m tt >>=_) (extensionality (maybe (λ _ → refl) refl)) ⟩ 
             m tt >>= pure 
           ≡⟨ >>=-idʳ (m tt) ⟩
             m tt
           ∎ 
  ; >>=-assoc      = λ k₁ k₂ m → extensionality λ where
      tt → begin
             (m tt >>= maybe′ (flip k₁ tt) (pure nothing)) >>= maybe′ (flip k₂ tt) (pure nothing)
           ≡⟨ >>=-assoc _ _ (m tt) ⟩
             m tt >>= (maybe′ (flip k₁ tt) (pure nothing) >=> maybe′ (flip k₂ tt) (pure nothing)) 
           ≡⟨ cong (m tt >>=_) (extensionality (maybe (λ _ → refl) refl)) ⟩ 
             m tt >>= maybe′ (λ x → k₁ x tt >>= maybe′ (flip k₂ tt) (pure nothing)) (pure nothing)
           ∎
  ; return-natural = λ where .commute x → refl
  } 

AbortHandler : Handler Abort ⊤ Maybe
Handler.F-functor   AbortHandler = maybe-functor
Handler.M-monad     AbortHandler = readerT-monad

Handler.hdl AbortHandler .αᶜ ⟨ `abort , k ⟩ = λ where tt → pure nothing

Handler.M-apply     AbortHandler                  = refl
Handler.hdl-commute AbortHandler f ⟨ `abort , k ⟩ = refl


handleAbort : Abort ∙ ε ≈ ε′ → Free ε′ A → Free ε (Maybe A)
handleAbort σ m = Handler.handle AbortHandler σ m tt


module Properties where

  open Handler AbortHandler

  modular : Modular
  modular = handle-modular 
 
  correct : Correct AbortTheory AbortHandler 
  correct (tt , refl) = refl

  handle-abort-is-nothing : (σ : Abort ∙ ε ≈ ε′) → handleAbort {A = A} σ (abort ⦃ _ , σ ⦄) ≡ pure nothing
  handle-abort-is-nothing {ε} σ =
    begin
      handleAbort σ abort
    ≡⟨⟩ 
      handle σ abort tt
    ≡⟨⟩
      handle σ (♯ (impure ⟨ `abort , ⊥-elim ⟩)) tt
    ≡⟨⟩ 
      handle′ (reorder σ (impure (inj ⟨ `abort , (λ x → fold-free pure inject (⊥-elim x)) ⟩))) tt
    ≡⟨⟩
      handle′ (fold-free pure (λ where .αᶜ → impure ∘ proj σ) $ impure (inj ⟨ `abort , (λ x → fold-free pure inject (⊥-elim x)) ⟩)) tt
    ≡⟨⟩ 
      handle′ (impure (proj σ (fmap (reorder σ) (inj ⟨ `abort , ((λ x → fold-free pure inject (⊥-elim x))) ⟩)))) tt
    ≡⟨ cong (flip handle′ tt ∘ impure ∘ proj σ)
       ( sym (inj-natural .commute {f = reorder σ} _)
       ) ⟩
      flip handle′ tt (impure (proj σ (inj (⟨ (`abort , (λ x → reorder σ $ fold-free pure inject (⊥-elim x))) ⟩)))) 
    ≡⟨ cong (flip handle′ tt ∘ impure)
         ( σ .union .equivalence _ .inverse .proj₂
           {x = ( injˡ {C₁ = Abort} ε ⟨ (`abort , (λ x → reorder σ $ fold-free pure inject (⊥-elim x))) ⟩)} refl
         ) ⟩
      flip handle′ tt (impure (injˡ {C₁ = Abort} ε ⟨ (`abort , (λ x → reorder σ $ fold-free pure inject (⊥-elim x))) ⟩)) 
    ≡⟨⟩ 
      pure nothing
    ∎
    where
      open Union
      open Inverse 
      open ≡-Reasoning
      instance inst : Abort ≲ _
      inst = _ , σ

  module _ ⦃ i : Abort ≲ ε′ ⦄ where 

    private instance ≲-inst-right : i .proj₁ ≲ (Abort ⊕ᶜ i .proj₁)
    ≲-inst-right = ≲-⊕ᶜ-right Abort
               
    private instance ≲-inst-left :  Abort ≲ (Abort ⊕ᶜ i .proj₁)
    ≲-inst-left = ≲-⊕ᶜ-left $ i .proj₁

    private instance inst : i .proj₁ ≲ ε′
    inst = Abort , union-comm (i .proj₂)

    reorder-catch-throw :
        ( ∀ (m : Free (Abort ⊕ᶜ i .proj₁) A)
          → ♯ (handle′ m tt) >>= maybe′ pure (abort >>= pure) ≡ m
        )
      → ∀ (m : Free ε′ A)
        -----------------------------------------------
      → ℋ⟦ m ⟧ tt >>= maybe′ pure (abort >>= pure) ≡ m
    reorder-catch-throw px m =
      begin
        ℋ⟦ m ⟧ tt >>= maybe′ pure (abort >>= pure)
      ≡⟨⟩ 
        ♯ (handle (i .proj₂) m tt) >>= maybe′ pure (abort >>= pure)
      ≡⟨⟩ 
        ♯ (handle′ (reorder (i .proj₂) m) tt) >>= maybe′ pure (abort >>= pure)
      ≡⟨ reorder-lemma (reorder (i .proj₂) m) ⟩
        reorder⁻¹ (i .proj₂) (♯ (handle′ (reorder (i .proj₂) m) tt) >>= maybe′ pure (abort >>= pure))
      ≡⟨ cong (reorder⁻¹ (i .proj₂)) (px (reorder (i .proj₂) m)) ⟩ 
        reorder⁻¹ (i .proj₂) (reorder (i .proj₂) m) 
      ≡⟨ reorder-inv (i .proj₂) m ⟩
        m
      ∎
      where
        open ≡-Reasoning

        reorder-lemma :
          ∀ (m : Free (Abort ⊕ᶜ i .proj₁) A)
            --------------------------------------------------------------------------
          → ♯ (handle′ m tt) >>= maybe′ pure (abort >>= pure)
            ≡ reorder⁻¹ (i .proj₂) (♯ (handle′ m tt) >>= maybe′ pure (abort >>= pure))
        reorder-lemma (pure x) = refl
        reorder-lemma (impure ⟨ inj₁ `abort , k ⟩) =
          begin
            ♯ (handle′ (impure ⟨ inj₁ `abort , k ⟩) tt) >>= maybe′ pure (abort >>= pure)
          ≡⟨⟩ 
            pure nothing >>= maybe′ pure (abort >>= pure)
          ≡⟨⟩ 
            abort >>= pure
          ≡⟨⟩ 
            ♯ (impure ⟨ `abort , ⊥-elim ⟩) >>= pure
          ≡⟨⟩
            impure (inj ⟨ (`abort , ♯ ∘ ⊥-elim) ⟩) >>= pure 
          ≡⟨⟩ 
            impure (fmap {F = ⟦ _ ⟧ᶜ} (_>>= pure) (inj ⟨ `abort , ♯ ∘ ⊥-elim ⟩))
          ≡⟨ cong impure (sym $ inj-natural .commute {f = _>>= pure} ⟨ `abort , (♯ ∘ ⊥-elim) ⟩) ⟩
            impure (inj (fmap {F = ⟦ _ ⟧ᶜ} (_>>= pure) ⟨ `abort , ♯ ∘ ⊥-elim ⟩))
          ≡⟨⟩ 
            impure (inj ⟨ `abort , ((♯ ∘ ⊥-elim) >=> pure) ⟩) 
          ≡⟨⟩ 
            impure (Union.proj⁻¹ (i .proj₂) (inj ⦃ ≲-inst-left ⦄ ⟨ `abort , ((♯ ∘ ⊥-elim) >=> pure) ⟩) ) 
          ≡⟨ cong (λ ○ → impure (Union.proj⁻¹ (i .proj₂) (inj ⟨ (`abort , ○) ⟩))) (extensionality λ()) ⟩
           impure (Union.proj⁻¹ (i .proj₂) (inj ⟨ `abort , hmap-free (Union.proj⁻¹ (i .proj₂)) ∘ (((♯ ∘ ⊥-elim) >=> pure)) ⟩))
          ≡⟨⟩ 
            hmap-free (Union.proj⁻¹ (i .proj₂)) (impure (inj ⟨ `abort , ((♯ ∘ ⊥-elim) >=> pure) ⟩)) 
          ≡⟨⟩ 
            hmap-free (Union.proj⁻¹ (i .proj₂)) (♯ (impure ⟨ `abort , ⊥-elim ⟩) >>= pure) 
          ≡⟨⟩ 
            hmap-free (Union.proj⁻¹ (i .proj₂)) ((abort >>= pure)) 
          ≡⟨⟩ 
            reorder⁻¹ (i .proj₂) (abort >>= pure) 
          ≡⟨⟩ 
             reorder⁻¹ (i .proj₂) (pure nothing >>= maybe′ pure (abort >>= pure))
          ≡⟨⟩ 
            reorder⁻¹ (i .proj₂) (♯ (handle′ (impure ⟨ inj₁ `abort , k ⟩) tt) >>= maybe′ pure (abort >>= pure))
          ∎
        reorder-lemma (impure ⟨ inj₂ c , k ⟩) =
          begin
            ♯ (handle′ (impure ⟨ inj₂ c , k ⟩) tt) >>= maybe′ pure (abort >>= pure)
          ≡⟨⟩
            ♯ (impure ⟨ c , flip handle′ tt ∘ k ⟩) >>= maybe′ pure (abort >>= pure)
          ≡⟨⟩ 
            impure (inj ⟨ c , ♯ ∘ flip handle′ tt ∘ k ⟩) >>= maybe′ pure (abort >>= pure)
          ≡⟨⟩ 
            impure (fmap {F = ⟦ _ ⟧ᶜ} (_>>= maybe′ pure (abort >>= pure)) (inj ⟨ c , ♯ ∘ flip handle′ tt ∘ k ⟩))
          ≡⟨ cong impure (sym $ inj-natural .commute {f = (_>>= maybe′ pure (abort >>= pure))} ⟨ c , ♯ ∘ flip handle′ tt ∘ k ⟩) ⟩ 
            impure (inj ⟨ c , ((♯ ∘ flip handle′ tt ∘ k) >=> maybe′ pure (abort >>= pure)) ⟩)
          ≡⟨ cong (λ ○ → impure (inj ⟨ c , ○ ⟩)) (extensionality (reorder-lemma ∘ k)) ⟩ 
            impure (inj ⟨ c , (λ x → reorder⁻¹ (i .proj₂) (♯ (handle′ (k x) tt) >>= maybe′ pure (abort >>= pure))) ⟩) 
          ≡⟨⟩
            reorder⁻¹ (i .proj₂) (♯ (handle′ (impure ⟨ inj₂ c , k ⟩) tt) >>= maybe′ pure (abort >>= pure))
          ∎

    catch-throw-lemma′ :
      ∀ (m : Free (Abort ⊕ᶜ i .proj₁) A)
        -----------------------------------------------------
      → ♯ (handle′ m tt) >>= maybe′ pure (abort >>= pure) ≡ m
    catch-throw-lemma′ (pure x)                     = refl
    catch-throw-lemma′ (impure ⟨ inj₁ `abort , k ⟩) =
      begin
        ♯ (handle′ (impure ⟨ inj₁ `abort , k ⟩) tt) >>= maybe′ pure (abort >>= pure)
      ≡⟨⟩
        pure nothing >>= maybe′ pure (abort >>= pure)
      ≡⟨⟩
        abort >>= pure
      ≡⟨ >>=-idʳ abort ⟩ 
        abort
      ≡⟨ cong (λ ○ → impure ⟨ inj₁ `abort , ○ ⟩) (extensionality λ()) ⟩ 
        impure ⟨ inj₁ `abort , k ⟩
      ∎
    catch-throw-lemma′ (impure ⟨ inj₂ c , k ⟩) =
      begin
        ♯ (handle′ (impure ⟨ inj₂ c , k ⟩) tt) >>= maybe′ pure (abort >>= pure)
      ≡⟨⟩ 
        ♯ (impure ⟨ c , flip handle′ tt ∘ k ⟩) >>= maybe′ pure (abort >>= pure) 
      ≡⟨⟩ 
        impure ⟨ inj₂ c , ♯ ∘ flip handle′ tt ∘ k ⟩ >>= maybe′ pure (abort >>= pure)
      ≡⟨⟩ 
        impure ⟨ inj₂ c , (♯ ∘ flip handle′ tt ∘ k) >=> maybe′ pure (abort >>= pure) ⟩ 
      ≡⟨ cong (λ ○ → impure ⟨ inj₂ c , ○ ⟩) (extensionality (catch-throw-lemma′ ∘ k)) ⟩
        impure ⟨ inj₂ c , k ⟩
      ∎

    catch-throw-lemma : ∀ (m : Free ε′ A) → ℋ⟦ m ⟧ tt >>= maybe′ pure (abort >>= pure) ≡ m
    catch-throw-lemma m = reorder-catch-throw catch-throw-lemma′ m

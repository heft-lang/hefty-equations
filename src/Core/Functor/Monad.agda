{-# OPTIONS --safe --without-K #-}

open import Core.Functor
open import Core.Functor.NaturalTransformation

open import Function

open import Relation.Unary
open import Relation.Binary.PropositionalEquality

module Core.Functor.Monad where

-- Monads on Set 
record Monad (F : Set → Set) : Set₁ where
  field
    {{ F-functor }} : Functor F

    return : A → F A
    _∗     : (A → F B) → (F A → F B)

  infixr 5 _>>=_ 
  _>>=_ : F A → (A → F B) → F B 
  _>>=_ = flip _∗

  _>=>_ : {C : Set} → (A → F B) → (B → F C) → A → F C
  (f >=> g) x = f x >>= g 

  _>>_ : F A → F B → F B
  x >> y = x >>= λ _ → y

  -- The "usual" monad laws (for Kleisli triples)
  field 
    >>=-idˡ : ∀ (x : A) (k : A → F B)
                ---------------------
              → return x >>= k ≡ k x
              
    >>=-idʳ : ∀ (m : F A)
                ----------------
              → m >>= return ≡ m
              
    >>=-assoc : ∀ {D} (k₁ : A → F B) (k₂ : B → F D) (m : F A) 
                  -------------------------------------------
                → (m >>= k₁) >>= k₂ ≡ m >>= (k₁ >=> k₂)  

  -- Naturality of return 
  field
    return-natural : Natural return

  is-functor : Functor F
  is-functor = F-functor 


open Monad ⦃...⦄ public

-- A monad morphism between monads M and N. We define it by requiring the
-- existence of a natural transformation θ from `M` to `N`, such that θ is a
-- monad morhpism if the induced functor on the respective Kleisli categories of
-- M and N is lawful
record MonadMorphism (M N : Set → Set)
  ⦃ _ : Monad M ⦄
  ⦃ _ : Monad N ⦄ : Set₁ where
  field
    Ψ         : ∀[ M ⇒ N ]
    Ψ-natural : Natural Ψ 

  ℱ[_] : (A → M B) → (A → N B)
  ℱ[_] = Ψ ∘_ 

  field 
    resp-unit : ∀ {A : Set}
                  -----------------------------
                → ℱ[ return {A = A} ] ≡ return
                            
    resp-join : ∀ {A B C : Set}
                → (f : A → M B) (g : B → M C)
                   ---------------------------------
                → ℱ[ f >=> g ] ≡ ℱ[ f ] >=> ℱ[ g ]  


open MonadMorphism public 

id-mm : ∀ {M} → ⦃ _ :  Functor M ⦄ → ⦃ _ : Monad M ⦄ → MonadMorphism M M 
id-mm = record
  { Ψ         = id
  ; Ψ-natural = λ where .commute x → refl
  ; resp-unit = refl
  ; resp-join = λ _ _ → refl
  } 

∘-mm : ∀ {M₁ M₂ M₃ : Set → Set}
       → ⦃ _ : Monad M₁ ⦄
       → ⦃ _ : Monad M₂ ⦄
       → ⦃ _ : Monad M₃ ⦄ 
       → MonadMorphism M₁ M₂
       → MonadMorphism M₂ M₃
       → MonadMorphism M₁ M₃ 
∘-mm {M₁} {M₂} {M₃} φ θ = record
  { Ψ         = θ .Ψ ∘ φ .Ψ
  ; Ψ-natural = ∘-natural (φ .Ψ) (θ .Ψ) (φ .Ψ-natural) (θ .Ψ-natural)
  ; resp-unit = trans (cong (θ .Ψ ∘_) (φ .resp-unit)) (θ .resp-unit)
  ; resp-join = ∘-resp-join
  }
  where
    ∘-resp-join :
      ∀ {A B C : Set}
      → (f : A → M₁ B) (g : B → M₁ C)
        ---------------------------------------------------------------------
      → (θ .Ψ ∘ φ .Ψ) ∘ (f >=> g) ≡ ((θ .Ψ ∘ φ .Ψ ∘ f) >=> (θ .Ψ ∘ φ .Ψ ∘ g))
    ∘-resp-join f g =
      begin
        (θ .Ψ ∘ φ .Ψ) ∘ (f >=> g)
      ≡⟨ cong (θ .Ψ ∘_) (φ .resp-join f g) ⟩
        θ .Ψ ∘ ((φ .Ψ ∘ f) >=> (φ .Ψ ∘ g))
      ≡⟨ θ .resp-join (φ .Ψ ∘ f) (φ .Ψ ∘ g) ⟩
        ((θ .Ψ ∘ φ .Ψ ∘ f) >=> (θ .Ψ ∘ φ .Ψ ∘ g))
      ∎
      where
        open ≡-Reasoning


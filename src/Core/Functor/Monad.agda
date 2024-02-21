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
    return : A → F A
    _∗     : (A → F B) → (F A → F B)

  infixr 5 _>>=_ 
  _>>=_ : F A → (A → F B) → F B 
  _>>=_ = flip _∗

  _>=>_ : {C : Set} → (A → F B) → (B → F C) → A → F C
  (f >=> g) x = f x >>= g 

  _>>_ : F A → F B → F B
  x >> y = x >>= λ _ → y

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

open Monad ⦃...⦄ public

-- A monad morphism between monads M and N. We define it by requiring the
-- existence of a natural transformation θ from `M` to `N`, such that θ is a
-- monad morhpism if the induced functor on the respective Kleisli categories of
-- M and N is lawful
record MonadMorphism (M N : Set → Set)
  ⦃ _ : Functor M ⦄
  ⦃ _ : Functor N ⦄
  ⦃ _ : Monad M ⦄
  ⦃ _ : Monad N ⦄ : Set₁ where
  field
    Ψ         : ∀[ M ⇒ N ]
    Ψ-natural : Natural Ψ 

  ℱ[_] : (A → M B) → (A → N B)
  ℱ[_] = Ψ ∘_ 

  field 
    respects-unit           : ∀ {A : Set}
                              -----------------------------
                            → ℱ[ return {A = A} ] ≡ return
                            
    respects-multiplication : ∀ {A B C : Set}
                            → (f : A → M B) (g : B → M C)
                              ---------------------------------
                            → ℱ[ f >=> g ] ≡ ℱ[ f ] >=> ℱ[ g ]  


open MonadMorphism public 

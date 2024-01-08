module Core.Functor where

open import Relation.Unary
open import Level renaming (suc to sℓ) 
open import Relation.Binary.PropositionalEquality

open import Data.Sum
open import Data.Product 

open import Function
open import Function.Construct.Identity
open import Function.Construct.Symmetry
open import Function.Construct.Composition

-- Lawful functors on Set, at any level 
record Functor {a b} (F : Set a → Set b) : Set (sℓ a ⊔ b) where  
  field
    fmap : {A B : Set a} → (A → B) → F A → F B

    -- Functor laws 
    fmap-id : ∀ {A : Set a} → ∀ (x : F A) → fmap id x ≡ x
    fmap-∘  :
      ∀ {A B C : Set a}
      → (f : A → B) (g : B → C)
      → (x : F A)
      → fmap g (fmap f x) ≡ fmap (g ∘ f) x 

open Functor ⦃...⦄ public

instance
  sum-functor : ∀ {a b} {F G : Set a → Set b} → ⦃ Functor F ⦄ → ⦃ Functor G ⦄ →  Functor (F ∪ G)
  Functor.fmap sum-functor f (inj₁ x) = inj₁ (fmap f x)
  Functor.fmap sum-functor f (inj₂ y) = inj₂ (fmap f y)
  Functor.fmap-id sum-functor (inj₁ x) = cong inj₁ (fmap-id x)
  Functor.fmap-id sum-functor (inj₂ y) = cong inj₂ (fmap-id y)
  Functor.fmap-∘ sum-functor f g (inj₁ x) = cong inj₁ (fmap-∘ f g x)
  Functor.fmap-∘ sum-functor f g (inj₂ y) = cong inj₂ (fmap-∘ f g y)

  id-functor : ∀ {a} → Functor {a} {a} λ x → x
  id-functor = record
    { fmap    = id
    ; fmap-id = λ x → refl
    ; fmap-∘  = λ f g x → refl
    } 

-- 
--   product-functor : ∀ {a b} {F G : Set a → Set b} → ⦃ Functor F ⦄ → ⦃ Functor G ⦄ →  Functor (F ∩ G)
--   product-functor = {!!}
--


-- Natural transformations between functors on Set 
record Natural {a b} {F G : Set a → Set b}
               ⦃ _ : Functor F ⦄ ⦃ _ : Functor G ⦄
               (θ : ∀[ F ⇒ G ]) : Set (sℓ a ⊔ b) where
  field
    commute : ∀ {X Y} {f : X → Y} → (x : F X) → θ (fmap f x) ≡ fmap f (θ x) 

open Natural public

record NaturalIsomorphism {a b} {F G : Set a → Set b}
                          ⦃ _ : Functor F ⦄ ⦃ _ : Functor G ⦄
                          (iso : ∀ x → F x ↔ G x) : Set (sℓ a ⊔ b) where
  field
    to-natural    : Natural (iso _ .Inverse.to)
    from-natural  : Natural (iso _ .Inverse.from) 

open NaturalIsomorphism public 


natiso-id : ∀ {a} → NaturalIsomorphism {a} ↔-id
natiso-id = record
  { to-natural   = λ where .commute _ → refl
  ; from-natural = λ where .commute _ → refl
  } 

natiso-sym : ∀ {a b} {F G : Set a → Set b}
               {F↔G : ∀ x → F x ↔ G x}
             → ⦃ _ : Functor F ⦄ → ⦃ _ : Functor G ⦄
             → NaturalIsomorphism F↔G
             → NaturalIsomorphism (↔-sym ∘ F↔G) 
natiso-sym {F = F} {G} {F↔G} natiso = record
  { to-natural   = natiso .from-natural
  ; from-natural = natiso .to-natural
  }

natiso-∘ : ∀ {a b} {F G H : Set a → Set b}
          {F↔G : ∀ x → F x ↔ G x} {G↔H : ∀ x → G x ↔ H x}
        → ⦃ _ : Functor F ⦄ → ⦃ _ : Functor G ⦄ → ⦃ _ : Functor H ⦄ 
        → NaturalIsomorphism F↔G → NaturalIsomorphism G↔H
        → NaturalIsomorphism λ x → F↔G x ↔-∘ G↔H x 
natiso-∘ {F = F} {G} {H} {F↔G} {G↔H} natiso₁ natiso₂ = record
  { to-natural   = λ where .commute → to-nat
  ; from-natural = λ where .commute → from-nat
  }
  where
    open Inverse
    open ≡-Reasoning 

    to-nat   : ∀ {X Y f} (x : F X) → (F↔G Y ↔-∘ G↔H Y) .to (fmap f x) ≡ fmap f ((F↔G X ↔-∘ G↔H X) .to x)
    to-nat {X}{Y}{f} x = begin
        (F↔G Y ↔-∘ G↔H Y) .to (fmap f x)
      ≡⟨⟩ {- Definition of ↔-∘ -} 
        G↔H Y .to (F↔G Y .to (fmap f x)) 
      ≡⟨ cong (G↔H Y .to) (natiso₁ .to-natural .commute x) ⟩
        G↔H Y .to (fmap f (F↔G X .to x))
      ≡⟨ natiso₂ .to-natural .commute _ ⟩ 
        fmap f (G↔H X .to (F↔G X .to x))
      ≡⟨⟩ {- Defintion of ↔-∘ -} 
        fmap f ((F↔G X ↔-∘ G↔H X) .to x) 
      ∎
    
    from-nat : ∀ {X Y f} (x : H X) → (F↔G Y ↔-∘ G↔H Y) .from (fmap f x) ≡ fmap f ((F↔G X ↔-∘ G↔H X) .from x)
    from-nat {X}{Y}{f} x = begin
        (F↔G Y ↔-∘ G↔H Y) .from (fmap f x)
      ≡⟨⟩ {- Definition of ↔-∘ -}
        F↔G Y .from (G↔H Y .from (fmap f x)) 
      ≡⟨ cong (F↔G Y .from) (natiso₂ .from-natural .commute x) ⟩
        F↔G Y .from (fmap f (G↔H X .from x))
      ≡⟨ natiso₁ .from-natural .commute _ ⟩
        fmap f (F↔G X .from (G↔H X .from x))
      ≡⟨⟩ {- Definition of ↔-∘ -} 
        fmap f ((F↔G X ↔-∘ G↔H X) .from x)
      ∎ 

-- Higher-order functors on Set. That is, functors over the category of functors
-- on Set
record HFunctor {a b} (H : (Set a → Set b) → Set a → Set b) : Set (sℓ (a ⊔ b)) where
  field
    -- H should respect functoriality
    ⦃ HF-functor ⦄ : ∀ {F} → ⦃ Functor F ⦄ → Functor (H F)

    -- A "higher-order" map, that associates natural transformations to natural
    -- transformations
    hmap : ∀ {F G} → ∀[ F ⇒ G ] → ∀[ H F ⇒ H G ]

    -- hmap should respect naturality
    hmap-natural :
      ∀ {F G}
      → ⦃ _ : Functor F ⦄ ⦃ _ : Functor G ⦄
      → (θ : ∀[ F ⇒ G ])
      → Natural θ → Natural (hmap θ)

open HFunctor ⦃...⦄ public 

variable a b : Level
         A : Set a
         B : Set b
         F G : Set a → Set b
         H H₁ H₂ : (Set a → Set b) → Set a → Set b

-- Pointed endofunctors on Set 
record Pointed (F : Set → Set) : Set₁ where
  field
    point : ∀[ id ⇒ F ]

open Pointed ⦃...⦄ public

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



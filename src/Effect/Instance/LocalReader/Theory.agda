{-# OPTIONS --without-K #-} 

open import Core.Functor

open import Effect.Base
open import Effect.Syntax.Hefty
open import Effect.Logic
open import Effect.Inclusion 

open import Effect.Theory.FirstOrder 
open import Effect.Theory.HigherOrder

open import Relation.Unary
open import Function

open import Data.List
open import Data.Product

-- Effect theory for the reader effect, with local operation, taken from 3MT
module Effect.Instance.LocalReader.Theory (R : Set) where


open import Effect.Instance.LocalReader.Syntax R
open Connectives

instance ⊑ᴴ-refl-inst : LocalReader ε ⊑ᴴ LocalReader ε
⊑ᴴ-refl-inst = ⊑ᴴ-refl

ask-query : Equationᴴ (LocalReader)
ask-query = left ≗ᴴ right 

  where
    ctx ret : Effect → TypeContext 1 → Set 
    ctx ε (A , _) = Hefty (LocalReader ε) A
    ret _ (A , _) = A 
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (LocalReader ε) ]

    left  _ m = askl >> m
    right _ m = m 


local-return : Equationᴴ (LocalReader)
local-return = left ≗ᴴ right

  where
    ctx ret : Effect → TypeContext 1 → Set
    ctx _ (A , _) = (R → R) × A
    ret _ (A , _) = A 
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (LocalReader ε) ]

    left  _ (f , x) = local f (return x)
    right _ (f , x) = return x 


ask-ask : Equationᴴ (LocalReader)
ask-ask = left ≗ᴴ right

  where
    ctx ret : Effect → TypeContext 1 → Set
    ctx ε (A , _) = R → R → Hefty (LocalReader ε) A 
    ret ε (A , _) = A 
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (LocalReader ε) ]

    left  _ k = askl >>= λ r → askl >>= k r
    right _ k = askl >>= λ r → k r r 

ask-bind : Equationᴴ (LocalReader)
ask-bind = left ≗ᴴ right
  where
    ctx ret : Effect → TypeContext 2 → Set 
    ctx ε (A , B , _) = Hefty (LocalReader ε) A × (A → R → Hefty (LocalReader ε) B)
    ret ε (A , B , _) = B
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (LocalReader ε) ]

    left  _ (m , k) = m >>= λ x → askl >>= λ r → k x r
    right _ (m , k) = askl >>= λ r → m >>= λ x → k x r 
    

local-bind : Equationᴴ (LocalReader)
local-bind = left ≗ᴴ right

  where
    ctx ret : Effect → TypeContext 2 → Set
    ctx ε (A , B , _) = Hefty (LocalReader ε) A × (A → Hefty (LocalReader ε) B) × (R → R) 
    ret ε (A , B , _) = B
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (LocalReader ε) ]

    left  _ (m , k , f) = local f (m >>= k)
    right _ (m , k , f) = local f m >>= λ x → local f (k x) 


local-ask : Equationᴴ (LocalReader)
local-ask = left ≗ᴴ right

  where
    ctx ret : Effect → TypeContext 0 → Set
    ctx _ _ = R → R
    ret _ _ = R
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (LocalReader ε) ]

    left  _ f = local f askl
    right _ f = askl >>= λ r → return (f r) 

local-local : Equationᴴ (LocalReader)
local-local = left ≗ᴴ right

  where
    ctx ret : Effect → TypeContext 1 → Set
    ctx ε (A , _) = (R → R) × (R → R) × Hefty (LocalReader ε) A 
    ret _ (A , _) = A
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (LocalReader ε) ]

    left  _ (f , g , m) = local (f ∘ g) m
    right _ (f , g , m) = local g (local f m) 
    

LocalReaderTheory : Theoryᴴ LocalReader
LocalReaderTheory =
  ∥  ask-query
  ∷ local-return
  ∷ ask-bind
  ∷ local-bind
  ∷ local-ask
  ∷ local-local
  ∷ [] ∥ᴴ 

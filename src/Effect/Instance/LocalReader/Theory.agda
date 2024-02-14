open import Core.Functor

open import Effect.Base
open import Effect.Syntax.Hefty
open import Effect.Logic
open import Effect.Inclusion 

open import Effect.Theory.FirstOrder 
open import Effect.Theory.HigherOrder

open import Relation.Unary

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
ask-ask = {!!}

ask-bind : Equationᴴ (LocalReader)
ask-bind = {!!}

local-bind : Equationᴴ (LocalReader)
local-bind = {!!}

local-ask : Equationᴴ (LocalReader)
local-ask = {!!} 

local-local : Equationᴴ (LocalReader)
local-local = {!!} 

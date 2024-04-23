{-# OPTIONS --without-K --type-in-type #-} 

open import Core.Functor
open import Core.Functor.Monad
open import Core.Ternary
open import Core.Logic

open import Effect.Base
open import Effect.Syntax.Hefty

open import Effect.Theory.FirstOrder 
open import Effect.Theory.HigherOrder

open import Effect.Relation.Ternary.HigherOrderSeparation
open import Effect.Relation.Binary.HigherOrderInclusion

open import Relation.Unary
open import Function

open import Data.List
open import Data.Product
open import Data.Fin

-- Effect theory for the reader effect, with local operation, taken from 3MT
module Effect.Instance.LocalReader.Theory (R : Set) where

open import Effect.Instance.LocalReader.Syntax R

module _ {η} ⦃ _ : LocalReader ≲ η ⦄ where

  ask-query : Equationᴴ η
  Δ′   ask-query = 1
  Γ′   ask-query ε (A , _) = Hefty (η ε) A
  R′   ask-query ε (A , _) = A
  lhsᴴ ask-query _ m       = askl >> m
  rhsᴴ ask-query _ m       = m

  local-return : Equationᴴ η
  Δ′   local-return = 1
  Γ′   local-return ε (A , _) = (R → R) × A
  R′   local-return ε (A , _) = A
  lhsᴴ local-return _ (f , x) = local f (return x)
  rhsᴴ local-return _ (f , x) = return x

  ask-ask : Equationᴴ η
  Δ′   ask-ask = 1
  Γ′   ask-ask ε (A , _) = R → R → Hefty (η ε) A
  R′   ask-ask ε (A , _) = A
  lhsᴴ ask-ask _ k = askl >>= λ r → askl >>= k r
  rhsᴴ ask-ask _ k = askl >>= λ r → k r r

  ask-bind : Equationᴴ η
  Δ′   ask-bind = 2
  Γ′   ask-bind ε (A , B , _) = Hefty (η ε) A × (A → R → Hefty (η ε) B)
  R′   ask-bind ε (A , B , _) = B
  lhsᴴ ask-bind _ (m , k) = m >>= λ x → askl >>= λ r → k x r
  rhsᴴ ask-bind _ (m , k) = askl >>= λ r → m >>= λ x → k x r

  local-bind : Equationᴴ η
  Δ′   local-bind = 2
  Γ′   local-bind ε (A , B , _) = Hefty (η ε) A × (A → Hefty (η ε) B) × (R → R)
  R′   local-bind ε (A , B , _) = B
  lhsᴴ local-bind _ (m , k , f) = local f (m >>= k)
  rhsᴴ local-bind _ (m , k , f) = local f m >>= local f ∘ k 

  local-ask : Equationᴴ η
  Δ′   local-ask = 0
  Γ′   local-ask _ _ = R → R
  R′   local-ask _ _ = R
  lhsᴴ local-ask _ f = local f askl
  rhsᴴ local-ask _ f = askl >>= return ∘ f

  local-local : Equationᴴ η
  Δ′   local-local = 1
  Γ′   local-local ε (A , _) = (R → R) × (R → R) × Hefty (η ε) A
  R′   local-local ε (A , _) = A
  lhsᴴ local-local _ (f , g , m) = local (f ∘ g) m
  rhsᴴ local-local _ (f , g , m) = local g (local f m)


LocalReaderTheory : Theoryᴴ LocalReader
arity LocalReaderTheory = Fin 7
eqs LocalReaderTheory zero                                     = nec ask-query
eqs LocalReaderTheory (suc zero)                               = nec local-return
eqs LocalReaderTheory (suc (suc zero))                         = nec ask-ask
eqs LocalReaderTheory (suc (suc (suc zero)))                   = nec ask-bind
eqs LocalReaderTheory (suc (suc (suc (suc zero))))             = nec local-bind
eqs LocalReaderTheory (suc (suc (suc (suc (suc zero)))))       = nec local-ask
eqs LocalReaderTheory (suc (suc (suc (suc (suc (suc zero)))))) = nec local-local


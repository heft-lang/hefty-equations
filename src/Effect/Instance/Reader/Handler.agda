open import Core.Functor
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
  correct (here refl) = refl


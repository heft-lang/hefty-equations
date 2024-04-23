{-# OPTIONS --without-K --type-in-type #-} 

open import Core.Functor
open import Core.Functor.Monad
open import Core.Signature
open import Core.Ternary
open import Core.Logic

open import Effect.Base
open import Effect.Syntax.Hefty

open import Effect.Theory.FirstOrder
open import Effect.Theory.HigherOrder
open import Effect.Instance.Catch.Syntax

open import Effect.Relation.Ternary.HigherOrderSeparation
open import Effect.Relation.Binary.HigherOrderInclusion

open import Data.Vec
open import Data.List
open import Data.Unit
open import Data.Product
open import Data.Fin

open import Relation.Unary

module Effect.Instance.Catch.Theory  where

module _ {η : Effectᴴ} ⦃ _ : Catch ≲ η ⦄ where
  
  bind-throw : Equationᴴ η
  Δ′   bind-throw               = 2
  Γ′   bind-throw ε (A , B , _) = A → Hefty (η ε) B
  R′   bind-throw ε (A , B , _) = B
  lhsᴴ bind-throw _ k           = throw >>= k
  rhsᴴ bind-throw _ _           = throw

  catch-return : Equationᴴ η
  Δ′   catch-return           = 1
  Γ′   catch-return ε (A , _) = Hefty (η ε) A × A
  R′   catch-return ε (A , _) = A
  lhsᴴ catch-return _ (m , x) = catch (return x) m
  rhsᴴ catch-return _ (_ , x) = return x

  catch-throw₁ : Equationᴴ η
  Δ′   catch-throw₁           = 1
  Γ′   catch-throw₁ ε (A , _) = Hefty (η ε) A
  R′   catch-throw₁ ε (A , _) = A
  lhsᴴ catch-throw₁ _ m       = catch throw m
  rhsᴴ catch-throw₁ _ m       = m

  catch-throw₂ : Equationᴴ η
  Δ′   catch-throw₂ = 1
  Γ′   catch-throw₂ ε (A , _) = Hefty (η ε) A
  R′   catch-throw₂ ε (A , _) = A
  lhsᴴ catch-throw₂ _ m = catch m throw
  rhsᴴ catch-throw₂ _ m = m

CatchTheory : Theoryᴴ Catch
arity CatchTheory = Fin 4
eqs CatchTheory zero                   = nec bind-throw
eqs CatchTheory (suc zero)             = nec catch-return
eqs CatchTheory (suc (suc zero))       = nec catch-throw₁
eqs CatchTheory (suc (suc (suc zero))) = nec catch-throw₂



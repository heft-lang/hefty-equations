open import Core.Functor

open import Effect.Base
open import Effect.Syntax.Hefty

open import Effect.Theory.FirstOrder
open import Effect.Theory.HigherOrder
open import Effect.Instance.Catch.Syntax

open import Data.Vec
open import Data.List
open import Data.Unit
open import Data.Product

open import Relation.Unary

module Effect.Instance.Catch.Theory where

-- This lets us use smart constructors when writing equations
instance ⊑ᴴ-refl-inst : Catch ε ⊑ᴴ Catch ε
⊑ᴴ-refl-inst = ⊑ᴴ-refl 

bind-throw : Equationᴴ Catch 
bind-throw = left ≗ᴴ right

  where 
    ctx ret  : Effect → TypeContext 2 → Set
    ctx ε (A , B , _) = A → Hefty (Catch ε) B
    ret ε (A , B , _) = B
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (Catch ε) ]

    left  _ k = throw >>= k 
    right _ _ = throw 


catch-return : Equationᴴ Catch
catch-return = left ≗ᴴ right

  where
    ctx ret : Effect → TypeContext 1 → Set
    ctx ε (A , _) = Hefty (Catch ε) A × A
    ret ε (A , _) = A
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (Catch ε) ]

    left  _ (m , x) = catch (return x) m
    right _ (_ , x) = return x 


catch-throw₁ : Equationᴴ Catch 
catch-throw₁ = left ≗ᴴ right 

  where
    ctx ret : Effect → TypeContext 1 → Set
    ctx ε (A , _) = Hefty (Catch ε) A
    ret ε (A , _) = A 
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (Catch ε) ]

    left  _ m = catch throw m 
    right _ m = m 


catch-throw₂ : Equationᴴ Catch
catch-throw₂ = left ≗ᴴ right

  where
    ctx ret : Effect → TypeContext 1 → Set
    ctx ε (A , _) = Hefty (Catch ε) A
    ret ε (A , _) = A
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (Catch ε) ]

    left  _ m = catch m throw 
    right _ m = m 


catch-catch : Equationᴴ Catch 
catch-catch = left ≗ᴴ right

  where
    ctx ret : Effect → TypeContext 2 → Set
    ctx ε (A , B , _) = Hefty (Catch ε) A × Hefty (Catch ε) A × (A → Hefty (Catch ε) B) × Hefty (Catch ε) B
    ret ε (A , B , _) = B 
    left right : {ε : Effect} → Π[ ctx ε ⇒ ret ε ⊢ Hefty (Catch ε) ]

    left  _ (m₁ , m₂ , k , m₃) = catch (catch m₁ m₂ >>= k) m₃
    right _ (m₁ , m₂ , k , m₃) = catch (m₁ >>= k) (catch (m₂ >>= k) m₃) 


CatchTheory : Theoryᴴ Catch
CatchTheory =
  ∥ bind-throw
  ∷ catch-return
  ∷ catch-throw₁
  ∷ catch-throw₂
--  ∷ catch-catch
  ∷ [] ∥ᴴ 

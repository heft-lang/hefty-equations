open import Core.Functor

open import Effect.Base
open import Hefty.Base

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
instance ⊑ᴴ-refl-inst : Catch ⊑ᴴ Catch
⊑ᴴ-refl-inst = ⊑ᴴ-refl 

bind-throw : Equationᴴ Catch 
bind-throw = left ≗ᴴ right

  where 
    ctx ret  : TypeContext 2 → Set
    ctx (A , B , _) = A → Hefty Catch B
    ret (A , B , _) = B
    left right : Π[ ctx ⇒ ret ⊢ Hefty Catch ]

    left  _ k = throw >>= k 
    right _ _ = throw 


catch-return : Equationᴴ Catch
catch-return = left ≗ᴴ right

  where
    ctx ret : TypeContext 1 → Set
    ctx (A , _) = Hefty Catch A × A
    ret (A , _) = A
    left right : Π[ ctx ⇒ ret ⊢ Hefty Catch ]

    left  _ (m , x) = catch (return x) m
    right _ (_ , x) = return x 


catch-throw₁ : Equationᴴ Catch 
catch-throw₁ = left ≗ᴴ right 

  where
    ctx ret : TypeContext 1 → Set
    ctx (A , _) = Hefty Catch A
    ret (A , _) = A 
    left right : Π[ ctx ⇒ ret ⊢ Hefty Catch ]

    left  _ m = catch throw m 
    right _ m = m 


catch-throw₂ : Equationᴴ Catch
catch-throw₂ = left ≗ᴴ right

  where
    ctx ret : TypeContext 1 → Set
    ctx (A , _) = Hefty Catch A
    ret (A , _) = A
    left right : Π[ ctx ⇒ ret ⊢ Hefty Catch ]

    left  _ m = catch m throw 
    right _ m = m 


catch-catch : Equationᴴ Catch 
catch-catch = left ≗ᴴ right

  where
    ctx ret : TypeContext 2 → Set
    ctx (A , B , _) = Hefty Catch A × Hefty Catch A × (A → Hefty Catch B) × Hefty Catch B
    ret (A , B , _) = B 
    left right : Π[ ctx ⇒ ret ⊢ Hefty Catch ]

    left  _ (m₁ , m₂ , k , m₃) = catch (catch m₁ m₂ >>= k) m₃
    right _ (m₁ , m₂ , k , m₃) = catch (m₁ >>= k) (catch (m₂ >>= k) m₃) 
   

CatchTheory : Theoryᴴ Catch
CatchTheory =
  ∥ bind-throw
  ∷ catch-return
  ∷ catch-throw₁
  ∷ catch-throw₂
  ∷ catch-catch
  ∷ []  ∥ᴴ 

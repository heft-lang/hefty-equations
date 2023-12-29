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

module Effect.Instance.Catch.Theory where

instance ⊑ᴴ-refl-inst : η ⊑ᴴ η
⊑ᴴ-refl-inst = ⊑ᴴ-refl 

bind-throw : Equationᴴ Catch {- 2
               (λ where (A ∷ B ∷ []) → A → Hefty Catch B)
               (λ where (A ∷ B ∷ []) → B) -} 
bind-throw = ? -- (λ where (_ ∷ _ ∷ []) k → throw >>= k) ≗ᴴ λ _ _ → throw

catch-return : Equationᴴ Catch -- 1 (λ where (A ∷ []) → Hefty Catch A × A ) λ where (A ∷ []) → A
catch-return = ? -- (λ where (A ∷ []) (m , x) → catch (return x) m) ≗ᴴ λ where (_ ∷ []) (m , x) → return x 

catch-throw₁ : Equationᴴ Catch -- 1 (λ where (A ∷ []) → Hefty Catch A) (λ where (A ∷ []) → A)
catch-throw₁ = ? -- (λ where (_ ∷ []) m → catch throw m) ≗ᴴ λ where (_ ∷ []) m → m 

catch-throw₂ : Equationᴴ Catch -- 1 (λ where (A ∷ []) → Hefty Catch A) (λ where (A ∷ []) → A)
catch-throw₂ = ? -- (λ where (_ ∷ []) m → catch m throw) ≗ᴴ λ where (_ ∷ []) m → m 

catch-catch : Equationᴴ Catch {- 2
                ((λ where (A ∷ B ∷ []) → Hefty Catch A
                                       × Hefty Catch A
                                       × (A → Hefty Catch B)
                                       × Hefty Catch B))
                (λ where (A ∷ B ∷ []) → B) -} 
catch-catch = ? {-
     (λ where (_ ∷ _ ∷ []) (m₁ , m₂ , k , m₃) → catch (catch m₁ m₂ >>= k) m₃)
  ≗ᴴ (λ where (_ ∷ _ ∷ []) (m₁ , m₂ , k , m₃) → catch (m₁ >>= k) (catch (m₂ >>= k) m₃))
-} 

CatchTheory : Theoryᴴ Catch
CatchTheory =
  ∥ bind-throw
  ∷ catch-return
  ∷ catch-throw₁
  ∷ catch-throw₂
  ∷ catch-catch
  ∷ []  ∥ᴴ 

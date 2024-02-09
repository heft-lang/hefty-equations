\begin{code}[hide]
{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}
module tex.sections.4-laws where

open import tex.sections.2-algebraic-effects
open import tex.sections.3-hefty-algebras

open import Function
open import Effect.Monad
open import Relation.Binary.PropositionalEquality
open import Data.Maybe using (Maybe; just; nothing)
open import Tactic.Cong

open FreeModule renaming (_𝓑_ to bindF) hiding (_>>_)
open HeftyModule renaming (_𝓑_ to bindH) hiding (_>>_; m; n; catch)


private variable M : Set → Set

open Universe ⦃ ... ⦄

module _ where
  open RawMonad hiding (pure)

  HeftyRawMonad : RawMonad (Hefty H)
  return HeftyRawMonad = pure
  RawMonad._>>=_ HeftyRawMonad = bindH
\end{code}


\section{Verifying Algebraic Laws for Higher-Order Effects}
\label{sec:laws}

A key idea behind algebraic effects is that we can state and prove algebraic laws about effectful operations.
In this section we show how to verify the lawfulness of catch , and compare the effort required to verify lawfulness using hefty algebras vs. a non-modular elaboration for catch.

The record type shown below defines the interface of a monad given by the record parameters \ab{M}, \ab{return}, and \ab{\_𝓑\_}.
The fields on the left below assert that \ab{M} has a \aF{𝑡ℎ𝑟𝑜𝑤} and \aF{𝑐𝑎𝑡𝑐ℎ} operation, as well as a \aF{run} function which runs a computation to yield a result \aF{R}~\as{:}~\ad{Set}~\as{→}~\ad{Set}.\footnote{The notation \as{⦃}~\ab{u}~\as{⦄}~\as{:}~\ad{Universe} treats the \ad{u} field as an \emph{instance} that can be automatically resolved in the scope of the \ad{CatchIntf} record type.}
On the right are the laws that constrain the behavior of the throw and catch operations.
The laws are borrowed from \citet{delaware2013meta}.
\\
\begin{minipage}{0.545\linewidth}
\footnotesize
\begin{code}
record  CatchIntf (M : Set → Set)
        (return  :  ∀ {A} → A → M A)
        (_𝓑_   :  ∀ {A B}
                 →  M A → (A → M B) → M B) : Set₁ where
  field  ⦃ u ⦄  : Universe
         𝑡ℎ𝑟𝑜𝑤   : {t : Ty} → M ⟦ t ⟧
         𝑐𝑎𝑡𝑐ℎ   : {t : Ty} → M ⟦ t ⟧ → M ⟦ t ⟧ → M ⟦ t ⟧
         R       : Set → Set
         run     : M A → R A
\end{code}
\end{minipage}
\hfill\vline\hfill
\begin{minipage}{0.445\linewidth}
\footnotesize
\begin{code}
         bind-throw  : {t₁ t₂ : Ty} (k : ⟦ t₁ ⟧ → M ⟦ t₁ ⟧)
           → run (𝑡ℎ𝑟𝑜𝑤 𝓑 k) ≡ run 𝑡ℎ𝑟𝑜𝑤
         catch-throw₁  : {t : Ty} (m : M ⟦ t ⟧)
           → run (𝑐𝑎𝑡𝑐ℎ 𝑡ℎ𝑟𝑜𝑤 m) ≡ run m
         catch-throw₂  : {t : Ty} (m : M ⟦ t ⟧)
           → run (𝑐𝑎𝑡𝑐ℎ m 𝑡ℎ𝑟𝑜𝑤) ≡ run m
         catch-return  : {t : Ty} (x : ⟦ t ⟧) (m : M ⟦ t ⟧)
           → run (𝑐𝑎𝑡𝑐ℎ (return x) m) ≡ run (return x)
\end{code}
\begin{code}[hide]
         catch-cong    : {t : Ty} (m₁ m₁′ m₂ m₂′ : M ⟦ t ⟧)
           → run m₁ ≡ run m₁′
           → run m₂ ≡ run m₂′
           → run (𝑐𝑎𝑡𝑐ℎ m₁ m₂) ≡ run (𝑐𝑎𝑡𝑐ℎ m₁′ m₂′)
\end{code}
\end{minipage}
\\
\Cref{fig:laws} (left) shows that the elaboration and handler from the previous section satisfy these laws.
The figure uses \af{‵throwᴴ} as an abbreviation for \af{↑}~\ac{throw}~\af{𝓑}~\af{⊥-elim}, \af{h} as an abbreviation of the handler for \af{hThrow}, and \af{e} as an abbreviation of \af{elaborate}.
The proofs are equational rewriting proofs akin to pen-and-paper proofs, except that each step is mechanically verified.
The equational rewriting steps use the \am{≡-Reasoning} module from the Agda standard library, and have the form \ab{t₁}~\af{≡⟨}~\ab{eq}~\af{⟩}~\ab{t₂} where \ab{t₁} is the term before the rewrite, \ab{t₂} is the term after, and \ab{eq} is a proof that \ab{t₁} and \ab{t₂} are equal.
The question is, how much overhead the hefty algebra encoding adds compared to the non-modular abbreviation of catch from \cref{sec:higher-order-effects}?
To answer this question, \cref{fig:laws} also contains the implementation and proof of a non-modular elaboration of catch (\ad{CatchImpl₁} on the right).
%
\begin{figure}
\centering
\begin{minipage}[t]{0.495\linewidth}%
\footnotesize%
\begin{AgdaMultiCode}%
\begin{code}[hide]
module CatchLawModule where
  open import Data.Empty
  open import Data.Unit
  open import Data.Maybe hiding (_>>=_)
  open import Data.Sum

  open CatchIntf
  open Abbreviation hiding (catch)
  open ElabModule
  open import tex.sections.Postulates.Extensionality
  open ≡-Reasoning

  ‵throwᴴ : ⦃ w : H  ∼  Lift Throw  ▹ H″ ⦄
           → Hefty H A
  ‵throwᴴ ⦃ w ⦄ = (↑ throw) 𝓑 ⊥-elim
    where open HeftyModule using (_𝓑_)


  module _ {H : Effectᴴ} {Δ : Effect} (E : Elaboration H (Throw ⊕ Δ)) where
    open HeftyModule using (pure) renaming (_𝓑_ to _𝓑⅋_)
    CatchImpl₀  :  ⦃ u : Universe ⦄
                →  CatchIntf  (Hefty (Lift Throw ∔ Catch ∔ H))
                              pure _𝓑⅋_
\end{code}
\begin{code}
    u             (CatchImpl₀ ⦃ u ⦄)    = u
    𝑡ℎ𝑟𝑜𝑤         CatchImpl₀            = ‵throwᴴ
    𝑐𝑎𝑡𝑐ℎ         CatchImpl₀            = ‵catch
    R             CatchImpl₀            = Free Δ ∘ Maybe 
    run           CatchImpl₀            =  h ∘ e

\end{code}
\begin{code}[hide]
      where
           h : ∀ {A} → Free (Throw ⊕ _) A → Free _ (Maybe A)
           e : ∀ {A} → Hefty (Lift Throw ∔ Catch ∔ _) A → Free (Throw ⊕ _) A
\end{code}
\begin{code}[hide]
           h m = (given hThrow handle m) tt
           e = elaborate (eLift ⋎ eCatch ⋎ E)
\end{code}
\begin{code}
    bind-throw    CatchImpl₀  k    = refl
    catch-return  CatchImpl₀  x m  = refl
\end{code}
\begin{code}
    catch-throw₁  CatchImpl₀  m    = begin
        h (e (‵catch ‵throwᴴ m))
      ≡⟨ refl ⟩
        h ((♯ h (e ‵throwᴴ)) 𝓑 maybe pure ((e m) 𝓑 pure))
      ≡⟨ cong! (Free-unitᵣ-≡ (e m)) ⟩
        h (e m) ∎
\end{code}
\begin{code}[hide]
      where
        h : ∀ {A} → Free (Throw ⊕ _) A → Free _ (Maybe A)
        e : ∀ {A} → Hefty (Lift Throw ∔ Catch ∔ _) A → Free (Throw ⊕ _) A
\end{code}
\begin{code}[hide]
        h m = (given hThrow handle m) tt
        e = elaborate (eLift ⋎ eCatch ⋎ E)
\end{code}
\begin{code}[hide]
        open FreeModule
\end{code}
\begin{code}
    catch-throw₂  CatchImpl₀  m    = begin
        h (e (‵catch m ‵throwᴴ))
      ≡⟨ refl ⟩
        h ((♯ h (e m)) 𝓑 maybe pure ((e ‵throwᴴ) 𝓑 pure))
      ≡⟨ cong (λ P → h ((♯ h (e m)) 𝓑 P))
           (extensionality (λ x →
             cong (λ P → maybe pure P x)
               (cong (impure (inj₁ throw))
                     (extensionality (λ x → ⊥-elim x))))) ⟩
        h ((♯ h (e m)) 𝓑 maybe pure ‵throw)
      ≡⟨ catch-throw-lem (e m) ⟩
        h (e m) ∎
\end{code}
\begin{code}[hide]
      where
        open FreeModule

        h : ∀ {A} → Free (Throw ⊕ _) A → Free _ (Maybe A)
        h m = (given hThrow handle m) tt
        e : ∀ {A} → Hefty (Lift Throw ∔ Catch ∔ _) A → Free (Throw ⊕ _) A
        e = elaborate (eLift ⋎ eCatch ⋎ E)
          
        catch-throw-lem : (m : Free (Throw ⊕ _) A)
                        → h ((♯ h m) 𝓑 maybe pure ‵throw)
                          ≡ (given hThrow handle m) tt
        catch-throw-lem (pure x)                = refl
        catch-throw-lem (impure (inj₁ throw) k) = refl
        catch-throw-lem (impure (inj₂ y) k) = cong (impure y) (extensionality (λ x → catch-throw-lem (k x)))
    catch-cong CatchImpl₀ m₁ m₁' m₂ m₂' eq₁ eq₂ = begin
        h (e (‵catch m₁ m₂))
      ≡⟨ refl ⟩
         h ((♯ h (e m₁)) 𝓑ᶠ maybe pure (e m₂ 𝓑ᶠ pure))
      ≡⟨ cong
           (λ P → h ((♯ h (e m₁)) 𝓑ᶠ P))
           (extensionality (λ x → cong (λ P → maybe pure P x) (Free-unitᵣ-≡ (e m₂)))) ⟩
         h ((♯ h (e m₁)) 𝓑ᶠ maybe pure (e m₂))
      ≡⟨ cong (λ P → h ((♯ P) 𝓑ᶠ maybe pure (e m₂))) eq₁ ⟩
         h ((♯ h (e m₁')) 𝓑ᶠ maybe pure (e m₂))
      ≡⟨ hThrow-bind-distr (♯ h (e m₁')) _ ⟩
         (h (♯ h (e m₁'))) 𝓑ᶠ maybe (h ∘ maybe pure (e m₂)) (pure nothing)
      ≡⟨ cong
           (λ P → (h (♯ (h (e m₁')))) 𝓑ᶠ maybe P (pure nothing))
           (extensionality (λ x → maybe-distr x pure (e m₂) h)) ⟩
         (h (♯ h (e m₁'))) 𝓑ᶠ maybe (maybe (h ∘ pure) (h (e m₂))) (pure nothing)
      ≡⟨ cong
           (λ P → (h (♯ (h (e m₁')))) 𝓑ᶠ maybe (maybe (h ∘ pure) P) (pure nothing))
           eq₂ ⟩
         (h (♯ h (e m₁'))) 𝓑ᶠ maybe (maybe (h ∘ pure) (h (e m₂'))) (pure nothing)
      ≡⟨ cong
           (λ P → (h (♯ (h (e m₁')))) 𝓑ᶠ maybe P (pure nothing))
           (extensionality (λ x → sym $ maybe-distr x pure (e m₂') h)) ⟩
         (h (♯ h (e m₁'))) 𝓑ᶠ maybe (h ∘ maybe pure (e m₂')) (pure nothing)
      ≡⟨ (sym $ hThrow-bind-distr (♯ h (e m₁')) _) ⟩
         h ((♯ h (e m₁')) 𝓑ᶠ maybe pure (e m₂'))
      ≡⟨ cong
           (λ P → h ((♯ h (e m₁')) 𝓑ᶠ P))
           (extensionality (λ x →
             cong
               (λ P → maybe pure P x)
               (sym $ Free-unitᵣ-≡ (e m₂')))) ⟩
        h ((♯ h (e m₁')) 𝓑ᶠ maybe pure (e m₂' 𝓑ᶠ pure))
      ≡⟨ refl ⟩
        h (e (‵catch m₁' m₂')) ∎
     where
       open HeftyModule renaming (_𝓑_ to _𝓑ᴴ_) hiding (m; n)
       open FreeModule renaming (_𝓑_ to _𝓑ᶠ_) hiding (Δ)
       
       h : ∀ {A} → Free (Throw ⊕ Δ) A → Free Δ (Maybe A)
       h m = (given hThrow handle m) tt
       
       e : ∀ {A} → Hefty (Lift Throw ∔ Catch ∔ _) A → Free (Throw ⊕ Δ) A
       e = elaborate (eLift ⋎ eCatch ⋎ E)

       maybe-distr : (x : Maybe A)
                     {B : Maybe A → Set}
                     (f : (a : A) → B (just a))
                     (b : B nothing)
                     (g : ∀ {x : Maybe A} → B x → C)
                   → g {x = x} (maybe {B = B} f b x) ≡ maybe (g ∘ f) (g b) x
       maybe-distr (just x) f b g = refl
       maybe-distr nothing f b g = refl

       hThrow-bind-distr : (m : Free (Throw ⊕ Δ) A) (k : A → Free (Throw ⊕ Δ) B)
                         → (given hThrow handle (m 𝓑ᶠ k)) tt
                           ≡ (given hThrow handle m) tt 𝓑ᶠ maybe (λ x → (given hThrow handle (k x)) tt) (pure nothing)
       hThrow-bind-distr (pure x) k = refl
       hThrow-bind-distr (impure (inj₁ throw) k₁) k = refl
       hThrow-bind-distr (impure (inj₂ y) k₁) k = cong (impure y) (extensionality (λ x → hThrow-bind-distr (k₁ x) k))
\end{code}
\end{AgdaMultiCode}
\end{minipage}%
\hfill\vline\hfill%
\begin{minipage}[t]{0.495\linewidth}%
\footnotesize%
\begin{AgdaMultiCode}%
\begin{code}[hide]
  module _ {Δ : Effect} where
    open FreeModule hiding (Δ)
    open Abbreviation
    CatchImpl₁  : ⦃ u : Universe ⦄
                →  CatchIntf  (Free (Throw ⊕ Δ))
                              pure _𝓑_
\end{code}
\begin{code}
    u             (CatchImpl₁ ⦃ u ⦄)   = u
    𝑡ℎ𝑟𝑜𝑤         CatchImpl₁           = ‵throw
    𝑐𝑎𝑡𝑐ℎ         CatchImpl₁           = catch
    R             CatchImpl₁           = Free Δ ∘ Maybe
    run           CatchImpl₁           = h
    
\end{code}
\begin{code}[hide]
      where h : ∀ {A} → Free (Throw ⊕ Δ) A → Free Δ (Maybe A)
            h m = (given hThrow handle m) tt
\end{code}
\begin{code}
    bind-throw    CatchImpl₁ k    = refl
    catch-return  CatchImpl₁ x m  = refl
    catch-throw₁  CatchImpl₁ m    = refl
\end{code}
\\[0.175em]
~
\\[0.175em]
~
\\[0.175em]
~
\\[0.175em]
\begin{code}
    catch-throw₂  CatchImpl₁ m    = begin
        h (catch m ‵throw)
      ≡⟨ refl ⟩
\end{code}
\\[0.175em]
~
\\[0.175em]
~
\\[0.175em]
~
\\[0.175em]
~
\\[0.175em]
\begin{code}
        h ((♯ h m) 𝓑 maybe pure ‵throw)
      ≡⟨ catch-throw-lem m ⟩
        h m ∎
\end{code}
\begin{code}[hide]
      where
        h : ∀ {A} → Free (Throw ⊕ Δ) A → Free Δ (Maybe A)
        h m = (given hThrow handle m) tt
          
        catch-throw-lem : (m : Free (Throw ⊕ Δ) A)
                        → h ((♯ h m) 𝓑 maybe pure ‵throw)
                          ≡ (given hThrow handle m) tt
        catch-throw-lem (pure x) = refl
        catch-throw-lem (impure (inj₁ throw) k) = refl
        catch-throw-lem (impure (inj₂ y) k) = cong (impure y) (extensionality (λ x → catch-throw-lem (k x)))
\end{code}
\begin{code}[hide]
    catch-cong CatchImpl₁ m₁ m₁′ m₂ m₂′ eq₁ eq₂ = begin
        h (catch m₁ m₂)
      ≡⟨ refl ⟩
        h ((♯ (h m₁)) 𝓑 maybe pure m₂)
      ≡⟨ cong (λ P → h ((♯ P) 𝓑 maybe pure m₂)) eq₁ ⟩
        h ((♯ h m₁′) 𝓑 maybe pure m₂)
      ≡⟨ h-distr (♯ h m₁′) (maybe pure m₂) ⟩
        (h (♯ h m₁′)) 𝓑 maybe (h ∘ maybe pure m₂) (pure nothing)
      ≡⟨ cong (λ P → (h (♯ h m₁′)) 𝓑 P)
           (extensionality (λ x →
             cong (λ P → maybe P (pure nothing) x)
               (extensionality (λ x →
                 maybe-distr x pure m₂ h)))) ⟩
        (h (♯ h m₁′)) 𝓑 maybe (maybe (h ∘ pure) (h m₂)) (pure nothing)
      ≡⟨ cong (λ P → (h (♯ h m₁′)) 𝓑 P)
           (extensionality (λ x →
             cong (λ P → maybe P (pure nothing) x)
               (extensionality (λ x →
                 cong (λ P → maybe _ P x) eq₂)))) ⟩
        (h (♯ h m₁′)) 𝓑 maybe (maybe (h ∘ pure) (h m₂′)) (pure nothing)
      ≡⟨ ( sym
         $ cong (λ P → (h (♯ h m₁′)) 𝓑 P)
             (extensionality (λ x →
               cong (λ P → maybe P (pure nothing) x)
                 (extensionality (λ x →
                   maybe-distr x pure m₂′ h))))) ⟩
        (h (♯ h m₁′)) 𝓑 maybe (h ∘ maybe pure m₂′) (pure nothing)
      ≡⟨ (sym $ h-distr (♯ h m₁′) (maybe pure m₂′)) ⟩
        h ((♯ h m₁′) 𝓑 maybe pure m₂′)
      ≡⟨ refl ⟩
        h (catch m₁′ m₂′) ∎
\end{code}
\begin{code}[hide]
      where
        h : ∀ {A} → Free (Throw ⊕ Δ) A → Free Δ (Maybe A)
        h m = (given hThrow handle m) tt

        maybe-distr : (x : Maybe A)
                      {B : Maybe A → Set}
                      (f : (a : A) → B (just a))
                      (b : B nothing)
                      (g : ∀ {x : Maybe A} → B x → C)
                    → g {x = x} (maybe {B = B} f b x) ≡ maybe (g ∘ f) (g b) x
        maybe-distr (just x) f b g = refl
        maybe-distr nothing f b g = refl

        h-distr : (m : Free (Throw ⊕ Δ) A) (k : A → Free (Throw ⊕ Δ) B)
                → h (m 𝓑 k) ≡ (h m) 𝓑 maybe (h ∘ k) (pure nothing)
        h-distr (pure x) k = refl
        h-distr (impure (inj₁ throw) k₁) k = refl
        h-distr (impure (inj₂ y) k₁) k = cong (impure y) (extensionality (λ x → h-distr (k₁ x) k))
\end{code}
\end{AgdaMultiCode}
\end{minipage}
\caption{Lawfulness for the modular elaboration (left) and the non-modular elaboration of catch (right)}
\label{fig:laws}
\end{figure}

The side-by-side comparison shows that hefty algebra elaborations add some administrative overhead.
In particular, elaborations introduce some redundant binds, as in the sub-term \as{(}\af{e}~\ab{m}\as{)}~\af{𝓑}~\ac{pure} of the term resulting from the first equational rewrite in \aF{catch-throw₁} on the left above.
These extraneous binds are rewritten away by applying the free monad right unit law (\ad{Free-unitᵣ-≡}).
Another source of overhead of using hefty algebras is that Agda is unable to infer that the term resulting from elaborating \af{‵throwᴴ} is equal to the term given by the smart constructor \af{‵throw}.
We prove this explicitly on the left above in the second-to-last equational rewrite of \aF{catch-throw₂}.
Both proofs make use of functional \ad{extensionality} (which is postulated since we cannot prove functional extensionality in general in Agda), and a straightforward \ad{catch-throw-lem} lemma that we prove by induction on the structure of the computation parameter of the lemma.

Except for the administrative overhead discussed above, the proofs have the same structure, and the effort of verifying algebraic laws for higher-order effects defined using hefty algebras is about the same as verifying algebraic laws for direct, non-modular encodings.



%%% Local Variables:
%%% reftex-default-bibliography: ("../references.bib")
%%% End:

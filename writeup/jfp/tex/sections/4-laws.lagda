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
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding (_++_)
open import Data.List renaming (map to map-list)
open import Data.Product
open import Data.Sum
open import Relation.Unary hiding (_∈_)
open import Data.List.Membership.Propositional

open import Level renaming (suc to sℓ)

open import Function.Construct.Identity
open import Function.Construct.Composition

open FreeModule renaming (_𝓑_ to bindF) hiding (_>>_)
open HeftyModule renaming (_𝓑_ to bindH) hiding (_>>_; m; n; catch)

open Abbreviation
open _∙_≈_ 

private variable M : Set → Set

open Universe ⦃ ... ⦄

module _ where
  open RawMonad hiding (pure)

  postulate instance FreeRawMonad : RawMonad (Free Δ)
  --FreeRawMonad = {!!} 

  HeftyRawMonad : RawMonad (Hefty H)
  HeftyRawMonad = record
    { rawApplicative = record
      { rawFunctor = record
        { _<$>_ = λ f x → bindH x λ v → pure (f v) }
        ; pure = pure
        ; _<*>_ = λ x y → bindH x λ f → bindH y λ v → pure (f v)
        }
    ; _>>=_ = bindH
    }

open RawMonad ⦃...⦄

_𝓑_ : Free Δ A → (A → Free Δ B) → Free Δ B
m 𝓑 k = m >>= k 

swap-⊕-↔ : {A : Set} → ⟦ Δ₁ ⊕ Δ₂ ⟧ A ↔ ⟦ Δ₂ ⊕ Δ₁ ⟧ A
swap-⊕-↔ = record
  { to        = λ where (inj₁ c , k) → inj₂ c , k
                        (inj₂ c , k) → inj₁ c , k 
  ; from      = λ where (inj₁ c , k) → inj₂ c , k
                        (inj₂ c , k) → inj₁ c , k 
  ; to-cong   = λ where refl → refl
  ; from-cong = λ where refl → refl
  ; inverse   = ( λ where {inj₁ c , k} refl → refl
                          {inj₂ c , k} refl → refl
                )
              , ( λ where {inj₁ c , k} refl → refl
                          {inj₂ c , k} refl → refl
                )
  } 
\end{code} 

\section{Modular Reasoning for Higher-Order Effects}

A key aspect of algebraic effects and handlers is to state and prove equational
\emph{laws} that characterize correct implementations of effectful
operations. Usually, an effect comes equipped with multiple laws that govern the
behavior of its operations, which we refer to a as a \emph{theory} of that
effect. Effect theories are closed under the co-product of effects, by combining
the equations into a new theory that contains all equations for both
effects~\citep{DBLP:journals/tcs/HylandPP06}. The concept of effect theories
extends to higher-order effects. Theories for higher-order effects too are
closed under sums of higher-order effect signatures. In this section, we discuss
how to define theories for algebraic effects in Agda (based on the definitions
used by \cite{DBLP:journals/pacmpl/YangW21}), and how to state and prove
correctness of implementations with respect to a given theory. We extend this
infrastructure to higher-order effects, to allow for modular reasoning about
elaborations of higher-order effects. 

To consider an example, the state effect, which comprises the $\af{get}$ and
$\af{put}$ operations, is typically associated with a set of equations (or laws)
that specify how implementations of the state effect ought to behave. One such
law is the \emph{get-get} law, which captures the intuition that the state
returned by two subsequent $\af{get}$ operation does not change if we do not use
the $\af{put}$ operation in between:
%
\begin{equation*}
  \af{get}\ 𝓑\ λ s →\ \af{get}\ 𝓑\ λ s′ →\ k\ s\ s′\ \equiv\ \af{get}\ 𝓑\ λ s →\ k\ s\ s
\end{equation*}
%
In a similar fashion, we an also state equations about higher-order effects. For
example, the following law is usually associated with the $\af{local}$ operation
of the reader effect, stating that transforming the context of a computation
that immediately returns a value has no effect:
%
\begin{equation*}
  \af{local}\ f\ (\mathbf{return}\ x)\ \equiv\ \mathbf{return}\ x
\end{equation*}

Correctness of an implementation of an algebraic effect with respect to a given
theory is defined by comparing the implementations of programs that are equal
under that theory. That is, if we can show that two programs are equal using the
equations of a theory for its effects, handling the effects should produce equal
results. For instance, a way to implement the state effect is by mapping
programs to functions of the form $\ab{S}~\to~S×A$. Such an implementation would
be correct if programs that are equal with respect to a theory of the state
effect are mapped to functions that give the same value and output state for
every input state.

For higher-order effects, correctness is defined in a similar manner. However,
since higher-order effects are implemented by elaborating into algebraic
effects, correctness of elaborations with respect to a higher-order effect
theory is defined by comparing the elaborated programs. Crucially, the
elaborated programs do not have to be syntactically equal, but rather we should
be able to prove them equal using a theory of the algebraic effects used to
implement a higher-order effect.

\subsection{Theories of Algebraic Effects}

Theories are collections of equations, so we start defining the type of
equations in Agda. At its core, an equation for the effect $Δ$ is given by a
pair of effect trees of the form $\ad{Free}~\ab{Δ}~A$, representing the left and
right hand side of the equation. However, looking at the \emph{get-get} law
above, we see that this equation contains a \emph{metavariable}, i.e.,
$\ab{k}$. Furthermore, looking at the type of $\ab{k}$,
$\ab{S}~\to~\ab{S}~\to~\ad{Free}~\ab{Δ}~\ab{A}$, we see that its type contains a
\emph{type metavariable}, i.e., $\ab{A}$. In general, an equation may refer to
any number of metavariables, which, in turn, may depend on any number of type
metavariables. Moreover, the type of the value returned by the left hand side
and right hand side of an equation may depend on these type metavariables as
well, as is the case for the \emph{get-get} law above.

This motivates the following definition of equations in Agda:
%
\begin{code}
record Equation (Δ : Effect) : Set₁ where
  field
    V        : ℕ
    Γ        : Vec Set V → Set
    R        : Vec Set V → Set 
    lhs rhs  : (vs : Vec Set V) → Γ vs → Free Δ (R vs)
\end{code}
%
An equation consists of five components. The field $\aF{V}$ defines the number
of type metavariables used in the equation. Then, the fields $\aF{Γ}$ and
$\aF{R}$ define the metavariables respectively return type of the equation. Both
may depend on the type metavariables of the equation, so they take a vector of
length $\aF{V}$ containing instantiations of all type metavariables as
input. Finally, the left hand side ($\aF{lhs}$) and right hand side ($\aF{rhs}$)
of the equation are then defined as values of type
$\ad{Free}~\ab{Δ}~(\aF{R}~vs)$, which take an instantiation of the type
metavariables and term metavariables as their input.

\paragraph*{Example}.
We consider how to define the \emph{get-get} as a value of type
$\ad{Equation}~\af{State}$. Recall that it depends on one type metavariable, and
one term metavariable. Furthermore, the return type of the programs on the left
and right hand sides is equal to the sole type metavariable:
%
\begin{AgdaAlign}
\begin{code}[hide]
open Equation
\end{code}
\begin{code}
get-get : Equation State
V    get-get = 1
Γ    get-get = λ where (A ∷ []) → ℕ → ℕ → Free State A
R    get-get = λ where (A ∷ []) → A
\end{code}
%
Since there is exactly one term metavariable, we equate $\aF{Γ}$ to the type of
$k$. For equations with more than one metavariable, we define $\aF{Γ}$ as a
product of the types of all term metavariables.  The $\aF{lhs}$ and $\aF{rhs}$
of the \emph{get-get} law are then defined as follows:
%
\begin{code} 
lhs  get-get (A ∷ []) k = ‵get 𝓑 λ s → ‵get 𝓑 λ s′ → k s s′ 
rhs  get-get (A ∷ []) k = ‵get 𝓑 λ s → k s s
\end{code}
\end{AgdaAlign}

\paragraph*{Modal Necessity}.
Consider the following equality: 
%
\begin{equation*}
  \af{get}\ 𝓑\ λ s\ →\ \af{get}\ 𝓑\ λ s′\ →\ \af{abort}\ \equiv\ \af{get}\ 𝓑\ λ s\ →\ \af{abort}  
\end{equation*}
%
We might expect to be able to prove this equality using the \emph{get-get} law,
but using the embedding of the law defined above---i.e., \af{get-get}---this is
not possible. The reason for this is that we cannot pick an appropriate
instantiation for the term metavariable $k$: it ranges over values of type
$\ab{S}~\to~\ab{S}~\to~Free State A$, inhibiting all references to effectful
operation that are not part of the state effect, such as $\af{abort}$.

Given an equation for the effect $Δ$, the solution is to view $Δ$ as a
\emph{lower bound}, rather than an exact specification of the effects used in
the left hand side and right hand side of the equation. Effectively, this means
that we close over all posible contexts of effects in which the equation can
occur. A useful abstraction that captures this pattern, which was also used by
\cite{DBLP:journals/jfp/AllaisACMM21} and \cite{DBLP:journals/pacmpl/RestPRVM22}
to respectively close over future contexts of free variables and canonical
forms, is to use a shallow embedding of the Kripke semantics of modal necessity:
%
\begin{code}
record □ (P : Effect → Set₁) (Δ : Effect) : Set₁ where
  field
    necessary : ∀ {Δ′} → ⦃ Δ ≲ Δ′ ⦄ → P Δ′
\end{code}
\begin{code}[hide]
open □ 
\end{code}
%
Intuitively the difference between terms of type $\ad{Equation}~\ab{Δ}$ and
$\ad{□}~\ad{Equation}~\ab{Δ}$ is that the former defines an equation relating
programs that have exactly effects $Δ$, while the latter defines an equation
relating programs that have \emph{at least} the effects $Δ$. The $\ad{□}$
modifier is a comonad, where the counit tells us that we can always view a lower
bound on effects as an exact specification by instantiating the extension
witness with a proof of reflexivity.
%
\begin{code}
extract : {P : Effect → Set₁} → □ P Δ → P Δ
extract px = px .necessary ⦃ ≲-refl ⦄
\end{code}
%
We can now redefine the \emph{get-get} law so that it applies to all programs
that have at least the $\ad{State}$ effect, but potentially other effects too.
%
\begin{code}
get-get′ : □ Equation State
V    (necessary get-get′       )             = 1
Γ    (necessary get-get′ {Δ′}  ) (A ∷ [])    = ℕ → ℕ → Free Δ′ A
R    (necessary get-get′       ) (A ∷ [])    = A
lhs  (necessary get-get′       ) (A ∷ []) k  = ‵get 𝓑 λ s → ‵get 𝓑 λ s′ → k s s′
rhs  (necessary get-get′       ) (A ∷ []) k  = ‵get 𝓑 λ s → k s s
\end{code}

\paragraph{Effect Theories}

\begin{code}
record Theory (Δ : Effect) : Set₁ where
  field
    equations : List (Equation Δ)

record Monotone {ℓ} (P : Effect → Set ℓ) : Set (sℓ 0ℓ ⊔ ℓ) where
  field
    weaken : Δ₁ ≲ Δ₂ → P Δ₁ → P Δ₂

open Monotone ⦃...⦄
open Equation
open Theory

instance eq-monotone : Monotone Equation
V    (Monotone.weaken eq-monotone w eq)       = V eq
Γ    (Monotone.weaken eq-monotone w eq)       = Γ eq
R    (Monotone.weaken eq-monotone w eq)       = R eq
lhs  (Monotone.weaken eq-monotone w eq) vs γ  = ♯_ ⦃ w ⦄ $ (lhs eq) vs γ
rhs  (Monotone.weaken eq-monotone w eq) vs γ  = ♯_ ⦃ w ⦄ $ (rhs eq) vs γ

instance □-monotone : {P : Effect → Set₁} → Monotone (□ P)
Monotone.weaken □-monotone w₁ px .necessary ⦃ w₂ ⦄ = px .necessary ⦃ ≲-trans w₁ w₂ ⦄

instance theory-monotone : Monotone Theory
equations (Monotone.weaken theory-monotone w T) = map-list (weaken w) (T .equations)

≲-⊕-left : Δ₁ ≲ (Δ₁ ⊕ Δ₂)
≲-⊕-left = _ , λ where .reorder → ↔-id _ 

≲-⊕-right : Δ₂ ≲ (Δ₁ ⊕ Δ₂)
≲-⊕-right = _ , λ where .reorder → swap-⊕-↔

≲-∙-left : Δ₁ ∙ Δ₂ ≈ Δ → Δ₁ ≲ Δ
≲-∙-left w = _ , w

≲-∙-right : Δ₁ ∙ Δ₂ ≈ Δ → Δ₂ ≲ Δ
≲-∙-right w = _ , λ where .reorder → w .reorder ↔-∘ swap-⊕-↔ 
\end{code}


Why the witness in the type of lhs and rhs? We want to state equations for all
programs that contain at least the effect $Δ$, but potentially more
effects. Although equations can be weakened to a larger set of effect, this does
not give the desired result, as equations containing meta-variables ranging over
effect trees in that case only apply to programs where the meta-variable is
instantiated to a weakened tree.

\begin{code}[hide]
open Equation 
open Theory 
\end{code}
\begin{code}
bind-throw : □ Equation Throw
V    (bind-throw .necessary)                      = 2
Γ    (bind-throw .necessary {Δ′}) (A ∷ B ∷ [])    = A → Free Δ′ B
R    (bind-throw .necessary)      (A ∷ B ∷ [])    = B
lhs  (bind-throw .necessary)      (_ ∷ _ ∷ []) k  = ‵throw >>= k
rhs  (bind-throw .necessary)      (_ ∷ _ ∷ []) k  = ‵throw
\end{code}


\begin{code}
_⟨+⟩_ : Theory Δ → Theory Δ → Theory Δ
equations (T₁ ⟨+⟩ T₂) = equations T₁ ++ equations T₂

_[+]_ : Theory Δ₁ → Theory Δ₂ → Theory (Δ₁ ⊕ Δ₂)
T₁ [+] T₂ = weaken ≲-⊕-left T₁ ⟨+⟩ weaken ≲-⊕-right T₂
\end{code}

\begin{code}
compose-theory : Δ₁ ∙ Δ₂ ≈ Δ → Theory Δ₁ → Theory Δ₂ → Theory Δ
compose-theory w T₁ T₂ = weaken (≲-∙-left w) T₁ ⟨+⟩ weaken (≲-∙-right w) T₂ 
\end{code}

\subsection{Syntactic Equivalence of Effectful Programs} 

\begin{code}[hide]
variable T T₁ T₂ T₃ T′ : Theory Δ
variable m m₁ m₂ m₃ m′ : Free Δ A

open ⟨_!_⇒_⇒_!_⟩

open Effect 
\end{code} 

\begin{AgdaAlign}
\begin{code}
data _≈⟨_⟩_ : (m₁ : Free Δ A) → Theory Δ → (m₂ : Free Δ A) → Set₁ where 
\end{code}

\begin{code}
  ≈-refl   : m  ≈⟨ T ⟩ m
  ≈-sym    : m₁ ≈⟨ T ⟩ m₂ → m₂ ≈⟨ T ⟩ m₁ 
  ≈-trans  : m₁ ≈⟨ T ⟩ m₂ → m₂ ≈⟨ T ⟩ m₃ → m₁ ≈⟨ T ⟩ m₃
\end{code}

\begin{code}
  ≈-cong  :  (op : Op Δ)
          →  (k₁ k₂ : Ret Δ op → Free Δ A)
          →  (∀ x → k₁ x ≈⟨ T ⟩ k₂ x) 
          →  impure (op , k₁) ≈⟨ T ⟩ impure (op , k₂) 
\end{code}

\begin{code}
  ≈-eq  :  (eq : Equation Δ)
        →  eq ∈ equations T 
        →  (vs : Vec Set (V eq))
        →  (γ : Γ eq vs)
        →  (k : R eq vs → Free Δ A)
        →  (lhs eq vs γ >>= k) ≈⟨ T ⟩ (lhs eq vs γ >>= k)  
\end{code}

\end{AgdaAlign}

\begin{code}
module ≈-Reasoning (T : Theory Δ) where

  infix 3 _≈_
  _≈_ : Free Δ A → Free Δ A → Set₁
  m₁ ≈ m₂ = m₁ ≈⟨ T ⟩ m₂

  begin_ : {m₁ m₂ : Free Δ A} → m₁ ≈ m₂ → m₁ ≈ m₂ 
  begin eq = eq 

  _∎ : (m : Free Δ A) → m ≈ m
  m ∎ = ≈-refl

  _≈⟪⟫_ : (m₁ : Free Δ A) {m₂ : Free Δ A} → m₁ ≈ m₂ → m₁ ≈ m₂  
  m₁ ≈⟪⟫ eq = eq

  _≈⟪_⟫_  : (m₁ {m₂ m₃} : Free Δ A) → m₁ ≈ m₂ → m₂ ≈ m₃ → m₁ ≈ m₃
  m₁ ≈⟪ eq₁ ⟫ eq₂ = ≈-trans eq₁ eq₂

  infix  1 begin_
  infixr 2 _≈⟪_⟫_ _≈⟪⟫_
  infix  3 _∎
\end{code}

(Prove two example programs equal perhaps?) 


\subsection{Handler Correctness}

An algebra over an effect Δ respects an equation of that effect iff folding with
the algebra gives the same result for the left hand side and right hand side of
the equation: 

\begin{code}
Respects : Alg Δ A → Equation Δ → Set₁
Respects {Δ = Δ} alg eq =
  ∀  {vs γ k}
  →  fold k alg (lhs eq vs γ)
  ≡  fold k alg (rhs eq vs γ) 
\end{code}

Correctness of an effect handler with respect to some theory: handling the
effect respects all equations in the theory.

\begin{code}
Correct : {P : Set} → Theory Δ → ⟨ A ! Δ ⇒ P ⇒ B ! Δ′ ⟩ → Set₁
Correct T H = ∀ {eq} → eq ∈ equations T → Respects (H .hdl) eq
\end{code}



%% 
%% 
%% \section{Verifying Algebraic Laws for Higher-Order Effects}
%% \label{sec:laws}
%% 
%% A key idea behind algebraic effects is that we can state and prove algebraic laws about effectful operations.
%% In this section we show how to verify the lawfulness of catch , and compare the effort required to verify lawfulness using hefty algebras vs. a non-modular elaboration for catch.
%% 
%% The record type shown below defines the interface of a monad given by the record parameters \ab{M}, \ab{return}, and \ab{\_𝓑\_}.
%% The fields on the left below assert that \ab{M} has a \aF{𝑡ℎ𝑟𝑜𝑤} and \aF{𝑐𝑎𝑡𝑐ℎ} operation, as well as a \aF{run} function which runs a computation to yield a result \aF{R}~\as{:}~\ad{Set}~\as{→}~\ad{Set}.\footnote{The notation \as{⦃}~\ab{u}~\as{⦄}~\as{:}~\ad{Universe} treats the \ad{u} field as an \emph{instance} that can be automatically resolved in the scope of the \ad{CatchIntf} record type.}
%% On the right are the laws that constrain the behavior of the throw and catch operations.
%% The laws are borrowed from \citet{delaware2013meta}.
%% \\
%% \begin{minipage}{0.545\linewidth}
%% \footnotesize
%% \begin{code}
%% record  CatchIntf (M : Set → Set)
%%         (return  :  ∀ {A} → A → M A)
%%         (_𝓑_   :  ∀ {A B}
%%                  →  M A → (A → M B) → M B) : Set₁ where
%%   field  ⦃ u ⦄  : Universe
%%          𝑡ℎ𝑟𝑜𝑤   : {t : Ty} → M ⟦ t ⟧ᵀ
%%          𝑐𝑎𝑡𝑐ℎ   : {t : Ty} → M ⟦ t ⟧ᵀ → M ⟦ t ⟧ᵀ → M ⟦ t ⟧ᵀ
%%          R       : Set → Set
%%          run     : M A → R A
%% \end{code}
%% \end{minipage}
%% \hfill\vline\hfill
%% \begin{minipage}{0.445\linewidth}
%% \footnotesize
%% \begin{code}
%%          bind-throw  : {t₁ t₂ : Ty} (k : ⟦ t₁ ⟧ᵀ → M ⟦ t₁ ⟧ᵀ)
%%            → run (𝑡ℎ𝑟𝑜𝑤 𝓑 k) ≡ run 𝑡ℎ𝑟𝑜𝑤
%%          catch-throw₁  : {t : Ty} (m : M ⟦ t ⟧ᵀ)
%%            → run (𝑐𝑎𝑡𝑐ℎ 𝑡ℎ𝑟𝑜𝑤 m) ≡ run m
%%          catch-throw₂  : {t : Ty} (m : M ⟦ t ⟧ᵀ)
%%            → run (𝑐𝑎𝑡𝑐ℎ m 𝑡ℎ𝑟𝑜𝑤) ≡ run m
%%          catch-return  : {t : Ty} (x : ⟦ t ⟧ᵀ) (m : M ⟦ t ⟧ᵀ)
%%            → run (𝑐𝑎𝑡𝑐ℎ (return x) m) ≡ run (return x)
%% \end{code}f
%% \begin{code}[hide]
%%          catch-cong    : {t : Ty} (m₁ m₁′ m₂ m₂′ : M ⟦ t ⟧ᵀ)
%%            → run m₁ ≡ run m₁′
%%            → run m₂ ≡ run m₂′
%%            → run (𝑐𝑎𝑡𝑐ℎ m₁ m₂) ≡ run (𝑐𝑎𝑡𝑐ℎ m₁′ m₂′)
%% \end{code}
%% \end{minipage}
%% \\
%% \Cref{fig:laws} (left) shows that the elaboration and handler from the previous section satisfy these laws.
%% The figure uses \af{‵throwᴴ} as an abbreviation for \af{↑}~\ac{throw}~\af{𝓑}~\af{⊥-elim}, \af{h} as an abbreviation of the handler for \af{hThrow}, and \af{e} as an abbreviation of \af{elaborate}.
%% The proofs are equational rewriting proofs akin to pen-and-paper proofs, except that each step is mechanically verified.
%% The equational rewriting steps use the \am{≡-Reasoning} module from the Agda standard library, and have the form \ab{t₁}~\af{≡⟨}~\ab{eq}~\af{⟩}~\ab{t₂} where \ab{t₁} is the term before the rewrite, \ab{t₂} is the term after, and \ab{eq} is a proof that \ab{t₁} and \ab{t₂} are equal.
%% The question is, how much overhead the hefty algebra encoding adds compared to the non-modular abbreviation of catch from \cref{sec:higher-order-effects}?
%% To answer this question, \cref{fig:laws} also contains the implementation and proof of a non-modular elaboration of catch (\ad{CatchImpl₁} on the right).
%% %
%% \begin{figure}
%% \centering
%% \begin{minipage}[t]{0.495\linewidth}%
%% \footnotesize%
%% \begin{AgdaMultiCode}%
%% \begin{code}[hide]
%% module CatchLawModule where
%%   open import Data.Empty
%%   open import Data.Unit
%%   open import Data.Maybe hiding (_>>=_)
%%   open import Data.Sum
%% 
%%   open CatchIntf
%%   open Abbreviation hiding (catch)
%%   open ElabModule
%%   open import tex.sections.Postulates.Extensionality
%%   open ≡-Reasoning
%% 
%%   ‵throwᴴ : ⦃ w : H  ∼  Lift Throw  ▹ H″ ⦄
%%            → Hefty H A
%%   ‵throwᴴ ⦃ w ⦄ = (↑ throw) 𝓑 ⊥-elim
%%     where open HeftyModule using (_𝓑_)
%% 
%% 
%%   module _ {H : Effectᴴ} {Δ : Effect} (E : Elaboration H (Throw ⊕ Δ)) where
%%     open HeftyModule using (pure) renaming (_𝓑_ to _𝓑⅋_)
%%     CatchImpl₀  :  ⦃ u : Universe ⦄
%%                 →  CatchIntf  (Hefty (Lift Throw ∔ Catch ∔ H))
%%                               pure _𝓑⅋_
%% \end{code}
%% \begin{code}
%%     u             (CatchImpl₀ ⦃ u ⦄)    = u
%%     𝑡ℎ𝑟𝑜𝑤         CatchImpl₀            = ‵throwᴴ
%%     𝑐𝑎𝑡𝑐ℎ         CatchImpl₀            = ‵catch
%%     R             CatchImpl₀            = Free Δ ∘ Maybe 
%%     run           CatchImpl₀            =  h ∘ e
%% 
%% \end{code}
%% \begin{code}[hide]
%%       where
%%            h : ∀ {A} → Free (Throw ⊕ _) A → Free _ (Maybe A)
%%            e : ∀ {A} → Hefty (Lift Throw ∔ Catch ∔ _) A → Free (Throw ⊕ _) A
%% \end{code}
%% \begin{code}[hide]
%%            h m = (given hThrow handle m) tt
%%            e = elaborate (eLift ⋎ eCatch ⋎ E)
%% \end{code}
%% \begin{code}
%%     bind-throw    CatchImpl₀  k    = refl
%%     catch-return  CatchImpl₀  x m  = refl
%% \end{code}
%% \begin{code}
%%     catch-throw₁  CatchImpl₀  m    = begin
%%         h (e (‵catch ‵throwᴴ m))
%%       ≡⟨ refl ⟩
%%         h ((♯ h (e ‵throwᴴ)) 𝓑 maybe pure ((e m) 𝓑 pure))
%%       ≡⟨ cong! (Free-unitᵣ-≡ (e m)) ⟩
%%         h (e m) ∎
%% \end{code}
%% \begin{code}[hide]
%%       where
%%         h : ∀ {A} → Free (Throw ⊕ _) A → Free _ (Maybe A)
%%         e : ∀ {A} → Hefty (Lift Throw ∔ Catch ∔ _) A → Free (Throw ⊕ _) A
%% \end{code}
%% \begin{code}[hide]
%%         h m = (given hThrow handle m) tt
%%         e = elaborate (eLift ⋎ eCatch ⋎ E)
%% \end{code}
%% \begin{code}[hide]
%%         open FreeModule
%% \end{code}
%% \begin{code}
%%     catch-throw₂  CatchImpl₀  m    = begin
%%         h (e (‵catch m ‵throwᴴ))
%%       ≡⟨ refl ⟩
%%         h ((♯ h (e m)) 𝓑 maybe pure ((e ‵throwᴴ) 𝓑 pure))
%%       ≡⟨ cong (λ P → h ((♯ h (e m)) 𝓑 P))
%%            (extensionality (λ x →
%%              cong (λ P → maybe pure P x)
%%                (cong (λ k → impure (inj₁ throw , k))
%%                      (extensionality (λ x → ⊥-elim x))))) ⟩
%%         h ((♯ h (e m)) 𝓑 maybe pure ‵throw)
%%       ≡⟨ catch-throw-lem (e m) ⟩
%%         h (e m) ∎
%% \end{code}
%% \begin{code}[hide]
%%       where
%%         open FreeModule
%% 
%%         h : ∀ {A} → Free (Throw ⊕ _) A → Free _ (Maybe A)
%%         h m = (given hThrow handle m) tt
%%         e : ∀ {A} → Hefty (Lift Throw ∔ Catch ∔ _) A → Free (Throw ⊕ _) A
%%         e = elaborate (eLift ⋎ eCatch ⋎ E)
%%           
%%         catch-throw-lem : (m : Free (Throw ⊕ _) A)
%%                         → h ((♯ h m) 𝓑 maybe pure ‵throw)
%%                           ≡ (given hThrow handle m) tt
%%         catch-throw-lem (pure x)                = refl
%%         catch-throw-lem (impure (inj₁ throw , k)) = refl
%%         catch-throw-lem (impure (inj₂ y , k)) = cong (impure ∘ (y ,_)) (extensionality (λ x → catch-throw-lem (k x)))
%%     catch-cong CatchImpl₀ m₁ m₁' m₂ m₂' eq₁ eq₂ = begin
%%         h (e (‵catch m₁ m₂))
%%       ≡⟨ refl ⟩
%%          h ((♯ h (e m₁)) 𝓑ᶠ maybe pure (e m₂ 𝓑ᶠ pure))
%%       ≡⟨ cong
%%            (λ P → h ((♯ h (e m₁)) 𝓑ᶠ P))
%%            (extensionality (λ x → cong (λ P → maybe pure P x) (Free-unitᵣ-≡ (e m₂)))) ⟩
%%          h ((♯ h (e m₁)) 𝓑ᶠ maybe pure (e m₂))
%%       ≡⟨ cong (λ P → h ((♯ P) 𝓑ᶠ maybe pure (e m₂))) eq₁ ⟩
%%          h ((♯ h (e m₁')) 𝓑ᶠ maybe pure (e m₂))
%%       ≡⟨ hThrow-bind-distr (♯ h (e m₁')) _ ⟩
%%          (h (♯ h (e m₁'))) 𝓑ᶠ maybe (h ∘ maybe pure (e m₂)) (pure nothing)
%%       ≡⟨ cong
%%            (λ P → (h (♯ (h (e m₁')))) 𝓑ᶠ maybe P (pure nothing))
%%            (extensionality (λ x → maybe-distr x pure (e m₂) h)) ⟩
%%          (h (♯ h (e m₁'))) 𝓑ᶠ maybe (maybe (h ∘ pure) (h (e m₂))) (pure nothing)
%%       ≡⟨ cong
%%            (λ P → (h (♯ (h (e m₁')))) 𝓑ᶠ maybe (maybe (h ∘ pure) P) (pure nothing))
%%            eq₂ ⟩
%%          (h (♯ h (e m₁'))) 𝓑ᶠ maybe (maybe (h ∘ pure) (h (e m₂'))) (pure nothing)
%%       ≡⟨ cong
%%            (λ P → (h (♯ (h (e m₁')))) 𝓑ᶠ maybe P (pure nothing))
%%            (extensionality (λ x → sym $ maybe-distr x pure (e m₂') h)) ⟩
%%          (h (♯ h (e m₁'))) 𝓑ᶠ maybe (h ∘ maybe pure (e m₂')) (pure nothing)
%%       ≡⟨ (sym $ hThrow-bind-distr (♯ h (e m₁')) _) ⟩
%%          h ((♯ h (e m₁')) 𝓑ᶠ maybe pure (e m₂'))
%%       ≡⟨ cong
%%            (λ P → h ((♯ h (e m₁')) 𝓑ᶠ P))
%%            (extensionality (λ x →
%%              cong
%%                (λ P → maybe pure P x)
%%                (sym $ Free-unitᵣ-≡ (e m₂')))) ⟩
%%         h ((♯ h (e m₁')) 𝓑ᶠ maybe pure (e m₂' 𝓑ᶠ pure))
%%       ≡⟨ refl ⟩
%%         h (e (‵catch m₁' m₂')) ∎
%%      where
%%        open HeftyModule renaming (_𝓑_ to _𝓑ᴴ_) hiding (m; n)
%%        open FreeModule renaming (_𝓑_ to _𝓑ᶠ_) hiding (Δ)
%%        
%%        h : ∀ {A} → Free (Throw ⊕ Δ) A → Free Δ (Maybe A)
%%        h m = (given hThrow handle m) tt
%%        
%%        e : ∀ {A} → Hefty (Lift Throw ∔ Catch ∔ _) A → Free (Throw ⊕ Δ) A
%%        e = elaborate (eLift ⋎ eCatch ⋎ E)
%% 
%%        maybe-distr : (x : Maybe A)
%%                      {B : Maybe A → Set}
%%                      (f : (a : A) → B (just a))
%%                      (b : B nothing)
%%                      (g : ∀ {x : Maybe A} → B x → C)
%%                    → g {x = x} (maybe {B = B} f b x) ≡ maybe (g ∘ f) (g b) x
%%        maybe-distr (just x) f b g = refl
%%        maybe-distr nothing f b g = refl
%% 
%%        hThrow-bind-distr : (m : Free (Throw ⊕ Δ) A) (k : A → Free (Throw ⊕ Δ) B)
%%                          → (given hThrow handle (m 𝓑ᶠ k)) tt
%%                            ≡ (given hThrow handle m) tt 𝓑ᶠ maybe (λ x → (given hThrow handle (k x)) tt) (pure nothing)
%%        hThrow-bind-distr (pure x) k = refl
%%        hThrow-bind-distr (impure (inj₁ throw , k₁)) k = refl
%%        hThrow-bind-distr (impure (inj₂ y , k₁)) k = cong (impure ∘ (y ,_)) (extensionality (λ x → hThrow-bind-distr (k₁ x) k))
%% \end{code}
%% \end{AgdaMultiCode}
%% \end{minipage}%
%% \hfill\vline\hfill%
%% \begin{minipage}[t]{0.495\linewidth}%
%% \footnotesize%
%% \begin{AgdaMultiCode}%
%% \begin{code}[hide]
%%   module _ {Δ : Effect} where
%%     open FreeModule hiding (Δ)
%%     open Abbreviation
%%     CatchImpl₁  : ⦃ u : Universe ⦄
%%                 →  CatchIntf  (Free (Throw ⊕ Δ))
%%                               pure _𝓑_
%% \end{code}
%% \begin{code}
%%     u             (CatchImpl₁ ⦃ u ⦄)   = u
%%     𝑡ℎ𝑟𝑜𝑤         CatchImpl₁           = ‵throw
%%     𝑐𝑎𝑡𝑐ℎ         CatchImpl₁           = catch
%%     R             CatchImpl₁           = Free Δ ∘ Maybe
%%     run           CatchImpl₁           = h
%%     
%% \end{code}
%% \begin{code}[hide]
%%       where h : ∀ {A} → Free (Throw ⊕ Δ) A → Free Δ (Maybe A)
%%             h m = (given hThrow handle m) tt
%% \end{code}
%% \begin{code}
%%     bind-throw    CatchImpl₁ k    = refl
%%     catch-return  CatchImpl₁ x m  = refl
%%     catch-throw₁  CatchImpl₁ m    = refl
%% \end{code}
%% \\[0.175em]
%% ~
%% \\[0.175em]
%% ~
%% \\[0.175em]
%% ~
%% \\[0.175em]
%% \begin{code}
%%     catch-throw₂  CatchImpl₁ m    = begin
%%         h (catch m ‵throw)
%%       ≡⟨ refl ⟩
%% \end{code}
%% \\[0.175em]
%% ~
%% \\[0.175em]
%% ~
%% \\[0.175em]
%% ~
%% \\[0.175em]
%% ~
%% \\[0.175em]
%% \begin{code}
%%         h ((♯ h m) 𝓑 maybe pure ‵throw)
%%       ≡⟨ catch-throw-lem m ⟩
%%         h m ∎
%% \end{code}
%% \begin{code}[hide]
%%       where
%%         h : ∀ {A} → Free (Throw ⊕ Δ) A → Free Δ (Maybe A)
%%         h m = (given hThrow handle m) tt
%%           
%%         catch-throw-lem : (m : Free (Throw ⊕ Δ) A)
%%                         → h ((♯ h m) 𝓑 maybe pure ‵throw)
%%                           ≡ (given hThrow handle m) tt
%%         catch-throw-lem (pure x) = refl
%%         catch-throw-lem (impure (inj₁ throw , k)) = refl
%%         catch-throw-lem (impure (inj₂ y , k)) = cong (impure ∘ (y ,_)) (extensionality (λ x → catch-throw-lem (k x)))
%% \end{code}
%% \begin{code}[hide]
%%     catch-cong CatchImpl₁ m₁ m₁′ m₂ m₂′ eq₁ eq₂ = begin
%%         h (catch m₁ m₂)
%%       ≡⟨ refl ⟩
%%         h ((♯ (h m₁)) 𝓑 maybe pure m₂)
%%       ≡⟨ cong (λ P → h ((♯ P) 𝓑 maybe pure m₂)) eq₁ ⟩
%%         h ((♯ h m₁′) 𝓑 maybe pure m₂)
%%       ≡⟨ h-distr (♯ h m₁′) (maybe pure m₂) ⟩
%%         (h (♯ h m₁′)) 𝓑 maybe (h ∘ maybe pure m₂) (pure nothing)
%%       ≡⟨ cong (λ P → (h (♯ h m₁′)) 𝓑 P)
%%            (extensionality (λ x →
%%              cong (λ P → maybe P (pure nothing) x)
%%                (extensionality (λ x →
%%                  maybe-distr x pure m₂ h)))) ⟩
%%         (h (♯ h m₁′)) 𝓑 maybe (maybe (h ∘ pure) (h m₂)) (pure nothing)
%%       ≡⟨ cong (λ P → (h (♯ h m₁′)) 𝓑 P)
%%            (extensionality (λ x →
%%              cong (λ P → maybe P (pure nothing) x)
%%                (extensionality (λ x →
%%                  cong (λ P → maybe _ P x) eq₂)))) ⟩
%%         (h (♯ h m₁′)) 𝓑 maybe (maybe (h ∘ pure) (h m₂′)) (pure nothing)
%%       ≡⟨ ( sym
%%          $ cong (λ P → (h (♯ h m₁′)) 𝓑 P)
%%              (extensionality (λ x →
%%                cong (λ P → maybe P (pure nothing) x)
%%                  (extensionality (λ x →
%%                    maybe-distr x pure m₂′ h))))) ⟩
%%         (h (♯ h m₁′)) 𝓑 maybe (h ∘ maybe pure m₂′) (pure nothing)
%%       ≡⟨ (sym $ h-distr (♯ h m₁′) (maybe pure m₂′)) ⟩
%%         h ((♯ h m₁′) 𝓑 maybe pure m₂′)
%%       ≡⟨ refl ⟩
%%         h (catch m₁′ m₂′) ∎
%% \end{code}
%% \begin{code}[hide]
%%       where
%%         h : ∀ {A} → Free (Throw ⊕ Δ) A → Free Δ (Maybe A)
%%         h m = (given hThrow handle m) tt
%% 
%%         maybe-distr : (x : Maybe A)
%%                       {B : Maybe A → Set}
%%                       (f : (a : A) → B (just a))
%%                       (b : B nothing)
%%                       (g : ∀ {x : Maybe A} → B x → C)
%%                     → g {x = x} (maybe {B = B} f b x) ≡ maybe (g ∘ f) (g b) x
%%         maybe-distr (just x) f b g = refl
%%         maybe-distr nothing f b g = refl
%% 
%%         h-distr : (m : Free (Throw ⊕ Δ) A) (k : A → Free (Throw ⊕ Δ) B)
%%                 → h (m 𝓑 k) ≡ (h m) 𝓑 maybe (h ∘ k) (pure nothing)
%%         h-distr (pure x) k = refl
%%         h-distr (impure (inj₁ throw , k₁)) k = refl
%%         h-distr (impure (inj₂ y , k₁)) k = cong (impure ∘ (y ,_)) (extensionality (λ x → h-distr (k₁ x) k))
%% \end{code}
%% \end{AgdaMultiCode}
%% \end{minipage}
%% \caption{Lawfulness for the modular elaboration (left) and the non-modular elaboration of catch (right)}
%% \label{fig:laws}
%% \end{figure}
%% 
%% The side-by-side comparison shows that hefty algebra elaborations add some administrative overhead.
%% In particular, elaborations introduce some redundant binds, as in the sub-term \as{(}\af{e}~\ab{m}\as{)}~\af{𝓑}~\ac{pure} of the term resulting from the first equational rewrite in \aF{catch-throw₁} on the left above.
%% These extraneous binds are rewritten away by applying the free monad right unit law (\ad{Free-unitᵣ-≡}).
%% Another source of overhead of using hefty algebras is that Agda is unable to infer that the term resulting from elaborating \af{‵throwᴴ} is equal to the term given by the smart constructor \af{‵throw}.
%% We prove this explicitly on the left above in the second-to-last equational rewrite of \aF{catch-throw₂}.
%% Both proofs make use of functional \ad{extensionality} (which is postulated since we cannot prove functional extensionality in general in Agda), and a straightforward \ad{catch-throw-lem} lemma that we prove by induction on the structure of the computation parameter of the lemma.
%% 
%% Except for the administrative overhead discussed above, the proofs have the same structure, and the effort of verifying algebraic laws for higher-order effects defined using hefty algebras is about the same as verifying algebraic laws for direct, non-modular encodings.
%% 
%% 
%% 
%% %%% Local Variables:
%% %%% reftex-default-bibliography: ("../references.bib")
%% %%% End:
%% 
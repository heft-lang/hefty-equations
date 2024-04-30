\begin{code}[hide]
{-# OPTIONS --overlapping-instances #-}
module tex.sections.4-laws where

open import tex.sections.2-algebraic-effects 
open import tex.sections.3-hefty-algebras 
open import Function
open import Effect.Monad
open import Relation.Binary.PropositionalEquality
open import Data.Maybe using (Maybe; just; nothing)
open import Tactic.Cong
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding (_++_ ; map ; _⋎_)
open import Data.List
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Relation.Unary hiding (_∈_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.Unit
open import Data.String

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
m 𝓑 k = bindF m k

_𝓑◂_ : Hefty H A → (A → Hefty H B) → Hefty H B
m 𝓑◂ k = bindH m k 

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
\label{sec:modular-reasoning}

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

private instance ≲-state-refl : State ≲ State
≲-state-refl = Nil , ∙-unitᵣ
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

\subsection{Modal Necessity}
\label{sec:modal-necessity}
Consider the following equality: 
%
\begin{equation}\label{eq:get-get-throw}
  \af{get}\ 𝓑\ λ s\ →\ \af{get}\ 𝓑\ λ s′\ →\ \af{throw}\ \equiv\ \af{get}\ 𝓑\ λ s\ →\ \af{throw}  
\end{equation}
%
We might expect to be able to prove this equality using the \emph{get-get} law,
but using the embedding of the law defined above---i.e., \af{get-get}---this is
not possible. The reason for this is that we cannot pick an appropriate
instantiation for the term metavariable $k$: it ranges over values of type
$\ab{S}~\to~\ab{S}~\to~Free State A$, inhibiting all references to effectful
operation that are not part of the state effect, such as $\af{throw}$.

Given an equation for the effect $Δ$, the solution is to view $Δ$ as a
\emph{lower bound}, rather than an exact specification of the effects used in
the left hand side and right hand side of the equation. Effectively, this means
that we close over all posible contexts of effects in which the equation can
occur. A useful abstraction that captures this pattern, which was also utilized
by \cite{DBLP:journals/jfp/AllaisACMM21} and
\cite{DBLP:journals/pacmpl/RestPRVM22} (where they respectively close over
future contexts of free variables and canonical forms of definitional
interpreters), is to use a shallow embedding of the Kripke semantics of modal
necessity:
%
\begin{code}
record □ (P : Effect → Set₁) (Δ : Effect) : Set₁ where
  constructor necessary 
  field
    □⟨_⟩ : ∀ {Δ′} → ⦃ Δ ≲ Δ′ ⦄ → P Δ′
\end{code}
\begin{code}[hide]
open □

≲-refl : Δ ≲ Δ
≲-refl = Nil , ∙Nil
  where
    ∙Nil : Δ ∙ Nil ≈ Δ 
    ∙Nil .reorder = record
      { to        = λ where (inj₁ c , k) → c , k
      ; from      = λ where (c , k) → inj₁ c , k 
      ; to-cong   = λ where refl → refl
      ; from-cong = λ where refl → refl
      ; inverse   = (λ where refl → refl) , λ where {inj₁ c , k} refl → refl
      } 
\end{code}
%
Intuitively, the $□$ modifier transforms, for any effect-indexed type, an
\emph{exact} specification of the set of effects to a \emph{lower bound}. For
equations, the difference between terms of type $\ad{Equation}~\ab{Δ}$ and
$\ad{□}~\ad{Equation}~\ab{Δ}$ amounts to the former defining an equation
relating programs that have exactly effects $Δ$, while the latter defines an
equation relating programs that have at least the effects $Δ$. The $\ad{□}$
modifier is a comonad, whose counit tells us that we can always view a lower
bound on effects as an exact specification by instantiating the extension
witness with a proof of reflexivity.
%
\begin{code}
extract : {P : Effect → Set₁} → □ P Δ → P Δ
extract px = □⟨ px ⟩ ⦃ ≲-refl ⦄
\end{code}
%
More generally, we can close values wrapped in the $□$ modifier using any
extension witness using the following operation: 
%
\begin{code}
close : {P : Effect → Set₁} → Δ₁ ≲ Δ₂ → □ P Δ₁ → P Δ₂
close w eq = (□⟨ eq ⟩) ⦃ w ⦄ 
\end{code}

We can now redefine the \emph{get-get} law so that it applies to all programs
that have at least the $\ad{State}$ effect, but potentially other effects too.
%
\begin{code}
get-get◂ : □ Equation State
V    □⟨ get-get◂ ⟩ = 1
Γ    □⟨ get-get◂ ⟩ (A ∷ [])    = ℕ → ℕ → Free _ A
R    □⟨ get-get◂ ⟩ (A ∷ [])    = A
lhs  □⟨ get-get◂ ⟩ (A ∷ []) k  = ‵get 𝓑 λ s → ‵get 𝓑 λ s′ → k s s′
rhs  □⟨ get-get◂ ⟩ (A ∷ []) k  = ‵get 𝓑 λ s → k s s
\end{code}
%
The above embedding of the \emph{get-get} law now actually does allow us to
prove the equality in \cref{eq:get-get-throw}; the term metavariable $k$ now
ranges over all continuations returning a tree of type
$\ad{Free}\ \ab{Δ′}\ \ab{A}$, for all $\ab{Δ′}$ such that
$\af{State}~\ad{≲}~\ab{Δ′}$. This way, we can instantiate $\ab{Δ′}$ with any set
of effects that includes both $\af{State}$ and $\af{Throw}$, allowing us to
instantiate $k$ as $\af{throw}$.

\subsection{Effect Theories}

Equations for an effect $Δ$ can be combined into a \emph{theory} for $Δ$. A
theory for the effect $Δ$ is simply a collection of equations, transformed using
the $\ad{□}$ modifier to ensure that term metavariables can range over programs
that include more effects than just $Δ$: 
%
\begin{code}
record Theory (Δ : Effect) : Set₁ where
  field
    arity      : Set 
    equations  : arity → □ Equation Δ
\end{code}
%
We can think of effect theories as defining a specification for how
implementations of an effect ought to behave. Although implementations may vary,
depending for example on whether they are tailored to readability or efficiency,
they should at least respect the equations of the theory of the effect they
implement. We will make precise what it means for an implementation to respect
an equation in \cref{sec:handler-correctness}.

Effect theories are closed under several composition operations that allow us to
combine the equations of different theories into single theory. The most basic
way of combining effect theories is by concatenating their respective lists of
equations.
%
\begin{code}[hide]
open Equation
open Theory
\end{code}
\begin{code}
_⟨+⟩_ : Theory Δ → Theory Δ → Theory Δ
arity      (T₁ ⟨+⟩ T₂)  = arity T₁ ⊎ arity T₂ 
equations  (T₁ ⟨+⟩ T₂)  (inj₁ a) = equations T₁ a
equations  (T₁ ⟨+⟩ T₂)  (inj₂ a) = equations T₂ a
\end{code}
%
This way of combining effects is somewhat limiting, as it imposes that the
theories we combine are theories for the exact same effect. It is more likely,
however, that we would want to combine theories for different effects. To do so
requires the ability to \emph{weaken} effect theories 

\begin{code}
weaken-□ : {P : Effect → Set₁} → ⦃ Δ₁ ≲ Δ₂ ⦄ → □ P Δ₁ → □ P Δ₂ 
□⟨ weaken-□ ⦃ w ⦄ px ⟩ ⦃ w′ ⦄ = □⟨ px ⟩ ⦃ ≲-trans w w′ ⦄

weaken-theory : ⦃ Δ₁ ≲ Δ₂ ⦄ → Theory Δ₁ → Theory Δ₂
arity     (weaken-theory T) = arity T 
equations (weaken-theory T) = λ a → weaken-□ $ T .equations a 
\end{code}
%
Categorically speaking, the observation that for a given effect-indexed type $P$
we can transform a value of type $P\ \ab{Δ₁}$ to a value of type $P\ \ab{Δ₂}$ if
we know that $\ab{Δ₁}~\ad{≲}~\ab{Δ₂}$ is equivalent to saying that $P$ is a
functor from the category of containers and container morphisms to the categorie
of sets. From this perspective, the existence of weakening for free $\ad{Free}$,
as witnessed by the $\af{♯}$ operation, implies that it too is a such a functor.

With weakening for theories at our disposal, we can combine effect theories for
different effects into a theory ranging over their coproduct.  This requires us
to first define appropriate instances relating coproducts to effect inclusion:
%
\begin{code}
≲-⊕-left   : Δ₁ ≲ (Δ₁ ⊕ Δ₂)
≲-⊕-right  : Δ₂ ≲ (Δ₁ ⊕ Δ₂)
\end{code}
\begin{code}[hide]
≲-⊕-left  = _ , λ where .reorder → ↔-id _
≲-⊕-right = _ , λ where .reorder → swap-⊕-↔
\end{code}
%
With these instances in scope, it is straightforward to show that effect
theories are closed under the coproduct of effects, by summing the weakened
theories.
%
\begin{code}
_[+]_ : Theory Δ₁ → Theory Δ₂ → Theory (Δ₁ ⊕ Δ₂)
T₁ [+] T₂ = weaken-theory ⦃ ≲-⊕-left ⦄ T₁ ⟨+⟩ weaken-theory ⦃ ≲-⊕-right ⦄ T₂
\end{code}
%
While this operation is in principle sufficient for our purposes, it forces a
specific order on the effects of the combined theory. We can generalize the
operation above to allow for the effects of the combined theory to appear in any
order. This requires the following instances:
%
\begin{code}
≲-∙-left   : ⦃ Δ₁ ∙ Δ₂ ≈ Δ ⦄ →  Δ₁ ≲ Δ
≲-∙-right  : ⦃ Δ₁ ∙ Δ₂ ≈ Δ ⦄ →  Δ₂ ≲ Δ
\end{code}
\begin{code}[hide]
≲-∙-left ⦃ w ⦄ = _ , w
≲-∙-right ⦃ w ⦄ = _ , λ where .reorder → w .reorder ↔-∘ swap-⊕-↔ 
\end{code}
%
Again, we show that effect theories are closed under coproducts up to reordering
by summing the weakened theories: 
%
\begin{code}
compose-theory : ⦃ Δ₁ ∙ Δ₂ ≈ Δ ⦄ → Theory Δ₁ → Theory Δ₂ → Theory Δ
compose-theory T₁ T₂ = weaken-theory ⦃ ≲-∙-left ⦄ T₁ ⟨+⟩ weaken-theory ⦃ ≲-∙-right ⦄ T₂ 
\end{code}

Since equations are defined by storing the syntax trees corresponding their left
hand side and right hand side, we would expect them to be weakenable
too. Indeed, we can define the following function witnessing weakenability of
equations.
%
\begin{code}
weaken-eq : ⦃ Δ₁ ≲ Δ₂ ⦄ → Equation Δ₁ → Equation Δ₂ 
\end{code}
\begin{code}[hide]
V (weaken-eq eq) = V eq
Γ (weaken-eq eq) = Γ eq
R (weaken-eq eq) = R eq
lhs (weaken-eq eq) = λ vs γ → ♯ lhs eq vs γ
rhs (weaken-eq eq) = λ vs γ → ♯ rhs eq vs γ
\end{code}
%
This begs the question: why would we opt to rely on weakenability of the $□$
modifier to show that theories are weakenable rather than using $\af{weaken-eq}$
directly? Although the latter approach would indeed allow us to define
composition of effect theories as well as to apply equations to programs that
have more effects than the effect the equation was originally defined for, the
possible ways we can instantiate term metavariables remains too
restrictive. That is, we still would not be able to prove the equality in
\cref{eq:get-get-throw}. Despite the fact that we can weaken the \emph{get-get}
law so that it applies to programs that use the $\ad{Throw}$ effect as well,
instantiations of $k$ will be limited to weakened effect trees, precluding any
instantiation that use operations of effects other than $\ad{State}$, such as
$\af{throw}$.

Finally, we must define what it means for a theory to be included in a bigger
theory. Given two theories, $\ab{T₁}$ and $\ab{T₂}$, ranging over effects
$\ab{Δ₁}$ and $\ab{Δ₂}$ respectively, we say that $\ab{T₁}$ is a
\emph{sub-theory} of $\ab{T₂}$ if (1) $Δ₁$ is a sub-effect of $Δ₂$, and all
equations of $\ab{T₁}$ are, in their weakened form, also part of $\ab{T₂}$. The
following record type captures this definition of sub-theories in Agda:
\todo{UPDATE!}
%
\begin{code}[hide]
variable T T₁ T₂ T₃ T′ : Theory Δ
variable m m₁ m₂ m₃ m′ : Free Δ A

open ⟨_!_⇒_⇒_!_⟩

open Effect 
\end{code}
\begin{code}
_◄_ : □ Equation Δ → Theory Δ → Set₁
eq ◄ T = ∃ λ a → T .equations a ≡ eq  
\end{code}
%
Here, the field $\aF{ext}$ witnesses that the effects of $\ab{T₁}$ are included
in the effects of $\ab{T₂}$, while the $\aF{sub}$ field transforms proofs that
an equation is included in $\ab{T₁}$ into a proof that its weakened form is
included in $\ab{T₂}$. 

\subsection{Syntactic Equivalence of Effectful Programs} 

As discussed, propositional equality of effectful programs is too strict, as it
precludes us from proving equalities that rely on a semantic understanding of
the effects involved, such as the equality in \cref{eq:eq-get-get-throw}. The
solution is to define an inductive relation that captures syntactic equivalence
modulo some effect theory. We base our definition of syntactic equality of
effectful programs on the relation defining equivalent computations by
\cite{DBLP:journals/pacmpl/YangW21}, Definition 3.1, adapting their definition
where necessary to account for the use of modal necessity in the definition of
$\ad{Theory}$.
%
\begin{AgdaAlign}
\begin{code}
data _≈⟨_⟩_ {Δ Δ′} ⦃ _ : Δ ≲ Δ′ ⦄ : (m₁ : Free Δ′ A) → Theory Δ → (m₂ : Free Δ′ A) → Set₁ where 
\end{code}
%
A value of type $\ab{m₁}~\ad{≈⟨}~\ab{T}~\ad{⟩}~\ab{m₂}$ witnesses that programs
$\ab{m₁}$ and $\ab{m₂}$ are equal modulo the equations of theory $\ab{T}$. The
first three constructors ensure that it is an equivalence relation.
%
\begin{code}
  ≈-refl   : m  ≈⟨ T ⟩ m
  ≈-sym    : m₁ ≈⟨ T ⟩ m₂ → m₂ ≈⟨ T ⟩ m₁ 
  ≈-trans  : m₁ ≈⟨ T ⟩ m₂ → m₂ ≈⟨ T ⟩ m₃ → m₁ ≈⟨ T ⟩ m₃
\end{code}
%
Then, we add the following congruence rule, that establish that we can prove
equality of two programs starting with the same operation by proving that the
continuations yield equal programs for every possible value. 
%
\begin{code}
  ≈-cong  :  (op : Op Δ′)
          →  (k₁ k₂ : Ret Δ′ op → Free Δ′ A)
          →  (∀ x → k₁ x ≈⟨ T ⟩ k₂ x) 
          →  impure (op , k₁) ≈⟨ T ⟩ impure (op , k₂) 
\end{code}
%
The final constructor allows to prove equality of programs by reifying equations
of an effect theory. 
%
\begin{code}
  ≈-eq  :  (eq : □ Equation Δ)
        →  (px : eq ◄ T)  
        →  (vs : Vec Set (V (□⟨ eq ⟩)))
        →  (γ : Γ (□⟨ eq ⟩) vs)
        →  (k : R (□⟨ eq ⟩) vs → Free Δ′ A)
        →  (lhs (□⟨ eq ⟩) vs γ 𝓑 k) ≈⟨ T ⟩ (rhs (□⟨ eq ⟩) vs γ 𝓑 k)  
\end{code}
\end{AgdaAlign}
%
Fundamentally, the $\ac{≈-eq}$ constructor equates the left hand side and right
hand side of any given equation. Due to the use of the $\ad{□}$ modifier, when
proving equality with respect to a theory $T₂$ we can actually use equations of
any sub-theory $T₁$ to prove equality. The extension witness stored in the
sub-theory proof $\ab{sub}$ is used to close the equation $\ab{eq}$, allowing us
to prove equality of its left and right hand side with respect to any larger
theory that includes that equation.

The $\ac{≈-eq}$ lets us sequence the left and right hand sides of an
equation with an arbitrary continuation $\ab{k}$. 
\begin{code}[hide]
postulate 𝓑-idʳ-≈ : {T : Theory Δ} → ⦃ _ : Δ ≲ Δ′ ⦄ → (m : Free Δ′ A) → m ≈⟨ T ⟩ (m 𝓑 Free.pure) 
\end{code}
\begin{code}
use-equation  :  ⦃ _ : Δ ≲ Δ′ ⦄
              →  {T : Theory Δ}
              →  (eq : □ Equation Δ)
              →  eq ◄ T
              →  (vs : Vec Set (V □⟨ eq ⟩))
              →  {γ : Γ (□⟨ eq ⟩) vs}
              →  lhs (□⟨ eq ⟩) vs γ ≈⟨ T ⟩ rhs (□⟨ eq ⟩) vs γ
\end{code}
\begin{code}[hide]
use-equation eq px vs {γ} = ≈-trans (𝓑-idʳ-≈ _) (≈-trans (≈-eq eq px vs γ Free.pure) (≈-sym $ 𝓑-idʳ-≈ _))
\end{code}
%
The definition of \af{use-equation} follows immediately from the right-identity
law for monads, i.e., $m\ 𝓑\ \ac{pure} \equiv m$. 

To construct proofs of equality it is convenient to use the following set of
combinators to write proof terms in an equational style. They are completely
analogous to the combinators commonly used to construct proofs of Agda's
propositional equality. 
%
\begin{code}
module ≈-Reasoning (T : Theory Δ) ⦃ _ : Δ ≲ Δ′ ⦄ where 

  begin_ : {m₁ m₂ : Free Δ′ A} → m₁ ≈⟨ T ⟩ m₂ → m₁ ≈⟨ T ⟩ m₂ 
  begin eq = eq 

  _∎ : (m : Free Δ′ A) → m ≈⟨ T ⟩ m
  m ∎ = ≈-refl

  _≈⟪⟫_ : (m₁ : Free Δ′ A) {m₂ : Free Δ′ A} → m₁ ≈⟨ T ⟩ m₂ → m₁ ≈⟨ T ⟩ m₂  
  m₁ ≈⟪⟫ eq = eq

  _≈⟪_⟫_  : (m₁ {m₂ m₃} : Free Δ′ A) → m₁ ≈⟨ T ⟩ m₂ → m₂ ≈⟨ T ⟩ m₃ → m₁ ≈⟨ T ⟩ m₃
  m₁ ≈⟪ eq₁ ⟫ eq₂ = ≈-trans eq₁ eq₂
\end{code}
%
\begin{code}[hide]
  infix  1 begin_
  infixr 2 _≈⟪_⟫_ _≈⟪⟫_
  infix  3 _∎
\end{code}

We now have all the necessary tools to prove syntactic equality of programs
modulo a theory of their effect. To illustrate, we consider how to prove the
equation in \cref{eq:get-get-throw}. First, we define a theory for the
$\ad{State}$ effect containing the $\af{get-get◄}$ law. While this is not the
only law typically associated with $\ad{State}$, for this example it is enough
to only have the $\af{get-get}$ law. 
%
\begin{code}
StateTheory : Theory State
arity StateTheory         = ⊤ 
equations StateTheory tt  = get-get◂
\end{code}
%
Now to prove the equality in \cref{eq:get-get-throw} is simply a matter of
invoking the $\af{get-get}$ law. 
\begin{code}
get-get-throw :
     ⦃ _ : Throw ≲ Δ ⦄ ⦃ _ : State ≲ Δ ⦄
  →  (‵get 𝓑 λ s → ‵get 𝓑 λ s′ → ‵throw {A = A}) ≈⟨ StateTheory ⟩ (‵get 𝓑  λ s → ‵throw)
get-get-throw {A = A} = begin
    ‵get 𝓑 (λ s → ‵get 𝓑 (λ s′ → ‵throw))
  ≈⟪ use-equation get-get◂ (tt , refl) (A ∷ [])  ⟫
    ‵get 𝓑 (λ s → ‵throw)
  ∎ 
  where open ≈-Reasoning StateTheory
\end{code}

\subsection{Handler Correctness}
\label{sec:handler-correctness}

Broadly speaking, a handler is correct with respect to a given theory if
handling syntactically equal programs yields equal results. Since handlers are
defined as algebras over effect signatures, we start by defining what it means
for an algebra of an effect $Δ$ to respect an equation of the same effect,
adapting Definition 2.1 in the exposition by
\cite{DBLP:journals/pacmpl/YangW21}.
%
\begin{code}
Respects : Alg Δ A → Equation Δ → Set₁
Respects alg eq = ∀ {vs γ k} →
  fold k alg (lhs eq vs γ) ≡ fold k alg (rhs eq vs γ) 
\end{code}
%
An algebra $\ab{alg}$ respects an equation $\ab{eq}$ if folding with that
algebra produces propositionally equal results for the left and right hand side
of the equation, for all possible instantiations of its type and term
metavariables, and continuations $k$.

A handler $\ab{H}$ is correct with respect to a given theory $\ab{T}$ if its
algebra respects all equations of $\ab{T}$ (\cite{DBLP:journals/pacmpl/YangW21},
Definition 4.3). 
%
\begin{code}
Correct : {P : Set} → Theory Δ → ⟨ A ! Δ ⇒ P ⇒ B ! Δ′ ⟩ → Set₁
Correct T H = ∀ {eq} → eq ◄ T → Respects (H .hdl) (extract eq) 
\end{code}
%
We can now show that the handler for the $\ad{State}$ effect defined in
\cref{fig:state-effect-handler} is correct with respect to
$\af{StateTheory}$; the proof follows immediately by reflexivity.
%
\begin{code}
hStCorrect : Correct {A = A} {Δ′ = Δ} StateTheory hSt
hStCorrect (tt , refl) {_ ∷ []} {γ = k} = refl 
\end{code}

\subsection{Theories of Higher-Order Effects}

For the most part, equations and theories for higher-order effects are defined
in the same way as for first-order effects and support many of the same
operations. Indeed, the definition of equations ranging over higher-order
effects is exactly the same as its first-order counterpart, the only difference
being that the left-hand and right-hand side are now defined as Hefty trees:
%
\begin{code}
record Equationᴴ (H : Effectᴴ) : Set₁ where
  field
    V        : ℕ
    Γ        : Vec Set V → Set
    R        : Vec Set V → Set 
    lhs rhs  : (vs : Vec Set V) → Γ vs → Hefty H (R vs)
\end{code}
%
This definition of equations suffers the same problem when it comes to term
metavariables, which here too can only range over programs that exhibit the
exact effect that the equation is defined for. Again, we address the issue using
an embedding of modal necessity to close over all possible extensions of this
effect. The definition is analogous to the one in \cref{sec:modal-necessity},
but this time we use higher-order effect subtyping as the modal accessibility
relation:
%
\begin{code}
record ■ (P : Effectᴴ → Set₁) (H : Effectᴴ) : Set₁ where
  constructor necessary 
  field ■⟨_⟩ : ∀ {H′} → ⦃ H ≲ᴴ H′ ⦄ → P H′ 
\end{code}
%
To illustrate: we can define the \emph{catch-throw} law from the introduction of
this section as a value of type $\ad{■}~\ad{Equationᴴ}~\af{Catch}$ a
follows:~\footnote{For simplicities sake, we gloss over the use of type
  universes to avoid size issues here.}
%
\begin{code}[hide]
open ■
open Equationᴴ 

module _ ⦃ _ : Universe ⦄ where
  postulate catch◂ : Hefty H A → Hefty H A → Hefty H A
  postulate throw◂ : Hefty H A
\end{code}
\begin{code} 
  catch-throw : ■ Equationᴴ Catch
  V    ■⟨ catch-throw ⟩ = 1
  Γ    ■⟨ catch-throw ⟩ (A ∷ []) = Hefty _ A
  R    ■⟨ catch-throw ⟩ (A ∷ []) = A
  lhs  ■⟨ catch-throw ⟩ (A ∷ []) m = catch◂ throw◂ m
  rhs  ■⟨ catch-throw ⟩ (A ∷ []) m = m
\end{code} 
\begin{code}[hide]
open Equationᴴ
\end{code}

Theories of higher-order effects bundle extensible equations. The setup is the
same as for theories of first-order effects. 
%
\begin{code}
record Theoryᴴ (H : Effectᴴ) : Set₁ where
  field
    arity     : Set
    equations : arity → ■ Equationᴴ H 
\end{code}
%
The following predicate establishes that an equation is part of a theory. We
prove this fact by providing an arity whose corresponding equation is equal to
$ab{eq}$. 
%
\begin{code}[hide]
variable Th Th₁ Th₂ Th₃ Th′ : Theoryᴴ H
open Theoryᴴ
open ■
\end{code}
\begin{code}
_◄ᴴ_ : ■ Equationᴴ H → Theoryᴴ H → Set₁
eq ◄ᴴ Th = ∃ λ a → eq ≡ equations Th a 
\end{code}

\begin{code}[hide]
module _ where
  open Effectᴴ
\end{code}
%
Weakenability of theories of higher-order effects then follows from
weakenability of its equations.
%
\begin{code}
  weaken-■ : ∀ {P} → ⦃ H₁ ≲ᴴ H₂ ⦄ → ■ P H₁ → ■ P H₂
  ■⟨ weaken-■ ⦃ w  ⦄ px ⟩ ⦃ w′ ⦄ = ■⟨ px ⟩ ⦃ ≲ᴴ-trans w w′ ⦄

  weaken-theoryᴴ : ⦃ H₁ ≲ᴴ H₂ ⦄ → Theoryᴴ H₁ → Theoryᴴ H₂
  arity      (weaken-theoryᴴ Th)    = Th .arity
  equations  (weaken-theoryᴴ Th) a  = weaken-■ (Th .equations a)
\end{code}

Theories of higher-order effects can be combined using the following sum
operation. The resulting theory contains all equations of both argument
theories.
%
\begin{code}
  _⟨+⟩ᴴ_ : ∀[ Theoryᴴ ⇒ Theoryᴴ ⇒ Theoryᴴ ]
  arity      (Th₁ ⟨+⟩ᴴ Th₂)           = arity Th₁ ⊎ arity Th₂
  equations  (Th₁ ⟨+⟩ᴴ Th₂) (inj₁ a)  = equations Th₁ a
  equations  (Th₁ ⟨+⟩ᴴ Th₂) (inj₂ a)  = equations Th₂ a
\end{code}
%
Theories of higher-order effects are closed under sums of higher-order effect
theories as well. This operation is defined by appropriately weakening the
respective theories, for which we need the following lemmas witnessing that
higher-order effect signatures can be injected in a sum of signatures.
%
\begin{code}[hide]
  postulate 
\end{code}
\begin{code}
    ≲-∔-left   : H₁ ≲ᴴ (H₁ ∔ H₂)
    ≲-∔-right  : H₂ ≲ᴴ (H₁ ∔ H₂) 
\end{code}
%
The operation that combines theories under signature sums is then defined like
so.
%
\begin{code}
  _[+]ᴴ_ : Theoryᴴ H₁ → Theoryᴴ H₂ → Theoryᴴ (H₁ ∔ H₂)
  Th₁ [+]ᴴ Th₂
    = weaken-theoryᴴ ⦃ ≲-∔-left ⦄ Th₁ ⟨+⟩ᴴ weaken-theoryᴴ ⦃ ≲-∔-right ⦄ Th₂
\end{code}

\subsection{Equivalence of Programs with Higher-Order Effects}

We define the following inductive relation to capture equivalence of programs
with higher-order effects modulo the equations of a given theory.

\begin{AgdaAlign}
\begin{code}
  data _≅⟨_⟩_ ⦃ _ : H₁ ≲ᴴ H₂ ⦄
    : (m₁ : Hefty H₂ A) → Theoryᴴ H₁ → (m₂ : Hefty H₂ A) → Set₁ where
\end{code}
%
To ensure that it is indeed an equivalence relation, we include constructors for
reflexivity, symmetry, and transitivity. 
%
\begin{code}
   ≅-refl   :  ∀  {m : Hefty H₂ A}
               →  m ≅⟨ Th ⟩ m
\end{code}
\begin{code}
   ≅-sym    :  ∀  {m₁ : Hefty H₂ A} {m₂}
               →  m₁ ≅⟨ Th ⟩ m₂
               →  m₂ ≅⟨ Th ⟩ m₁
\end{code}
\begin{code}
   ≅-trans  :  ∀  {m₁ : Hefty H₂ A} {m₂ m₃}
               →  m₁ ≅⟨ Th ⟩ m₂ → m₂ ≅⟨ Th ⟩ m₃
               →  m₁ ≅⟨ Th ⟩ m₃
\end{code}
%
Furthermore, we include the following congruence rule that equates two program
trees that have the same operation at the root, if their continuations are
equivalent for all inputs. 
%
\begin{code}
   ≅-cong   :     (op : Opᴴ H₂)
               →  (k₁ k₂ : Retᴴ H₂ op → Hefty H₂ A)
               →  (s₁ s₂ : (ψ : Fork H₂ op) → Hefty H₂ (Ty H₂ ψ))
               →  (∀ {x} → k₁ x ≅⟨ Th ⟩ k₂ x)
               →  (∀ {ψ} → s₁ ψ ≅⟨ Th ⟩ s₂ ψ)  
               →  impure (op , k₁ , s₁) ≅⟨ Th ⟩ impure ( op , k₂ , s₂ )
\end{code}
%
Finally, we include a constructor that equates two programs using an equation of
the theory.
%
\begin{code}
   ≅-eq     :     (eq : ■ Equationᴴ H₁)
               →  eq ◄ᴴ Th
               →  (vs : Vec Set (V ■⟨ eq ⟩))
               →  (γ : Γ ■⟨ eq ⟩ vs)
               →  (k : R ■⟨ eq ⟩ vs → Hefty H₂ A)
               →  (lhs ■⟨ eq ⟩ vs γ 𝓑◂ k) ≅⟨ Th ⟩ (rhs ■⟨ eq ⟩ vs γ 𝓑◂ k) 
\end{code}
\end{AgdaAlign}
%
We can define the same reasoning combinators to construct proofs of equivalence
for programs with higher-order effects. 

\begin{code}
module ≅-Reasoning ⦃ _ : H₁ ≲ᴴ H₂ ⦄ (Th : Theoryᴴ H₁) where

  begin_ : {m₁ m₂ : Hefty H₂ A} → m₁ ≅⟨ Th ⟩ m₂ → m₁ ≅⟨ Th ⟩ m₂ 
  begin eq = eq 

  _∎ : (c : Hefty H₂ A) → c ≅⟨ Th ⟩ c
  c ∎ = ≅-refl

  _≅⟪⟫_ : (m₁ : Hefty H₂ A) {m₂ : Hefty H₂ A} → m₁ ≅⟨ Th ⟩ m₂ → m₁ ≅⟨ Th ⟩ m₂  
  c₁ ≅⟪⟫ eq = eq

  _≅⟪_⟫_  : (c₁ {c₂ c₃} : Hefty H₂ A) → c₁ ≅⟨ Th ⟩ c₂ → c₂ ≅⟨ Th ⟩ c₃ → c₁ ≅⟨ Th ⟩ c₃
  c₁ ≅⟪ eq₁ ⟫ eq₂ = ≅-trans eq₁ eq₂
\end{code}
\begin{code}[hide]
  infix 1 begin_
  infixr 2 _≅⟪_⟫_ _≅⟪⟫_
  infix 3 _∎
\end{code}
%
\begin{code}[hide]
postulate 
  use-equationᴴ  :  ⦃ _ : H ≲ᴴ H′ ⦄
                 →  {T : Theoryᴴ H}
                 →  (eq : ■ Equationᴴ H)
                 →  eq ◄ᴴ T
                 →  (vs : Vec Set (V ■⟨ eq ⟩))
                 →  {γ : Γ (■⟨ eq ⟩) vs}
                 →  lhs (■⟨ eq ⟩) vs γ ≅⟨ T ⟩ rhs (■⟨ eq ⟩) vs γ

module _ ⦃ _ : Universe ⦄ where

  CatchTheory : Theoryᴴ Catch
  arity CatchTheory = ⊤
  equations CatchTheory tt = catch-throw

  postulate censor◂ : (String → String) → Hefty H A → Hefty H A 
\end{code}
%
To illustrate, we can prove that the programs
$\af{catch}~\af{throw}~(\af{censor}~\ab{f}~\ab{m})$ and
$\af{censor}~\ab{f}~\ab{m}$ are equal under a theory for the $af{Catch}$ effect
that contains the \emph{catch-throw} law.
%
\begin{code}

  catch-throw-censor :  ∀  {f} {m : Hefty H A}
                        →  ⦃ _ : Catch ≲ᴴ H ⦄ → ⦃ _ : Censor ≲ᴴ H ⦄
                        →  catch◂ throw◂ (censor◂ f m) ≅⟨ CatchTheory ⟩ censor◂ f m
  catch-throw-censor {A = A} {f = f} {m = m} =
    begin
      catch◂ throw◂ (censor◂ f m)
    ≅⟪ use-equationᴴ catch-throw (tt , refl) (A ∷ []) ⟫
      censor◂ f m
    ∎
    where open ≅-Reasoning _
\end{code}
%
The equivalence proof above makes, again, essential use of modal necessity. That
is, by closing over all possible extensions of the $\af{Catch}$ effe, the term
metavariable in the \emph{catch-throw} law to range over programs that have
higher-order effects other than $\af{Catch}$, which is needed to apply the law
if the second branch of the $\af{catch}$ operation contains the $\af{censor}$
operation.

\subsection{Correctness of Elaborations}

\begin{code}
Respectsᴴ : (_~_ : ∀ {A} → Free Δ A → Free Δ A → Set₁) → Algᴴ H (Free Δ) → Equationᴴ H → Set₁
Respectsᴴ _~_ alg eq =
  ∀ {δ γ} → cataᴴ Free.pure alg (lhs eq δ γ) ~ cataᴴ Free.pure alg (rhs eq δ γ)
\end{code}

\begin{code}
open Algᴴ

record _⊑_ (e₁ : □ (Elaboration H₁) Δ₁) (e₂ : □ (Elaboration H₂) Δ₂) : Set₁ where
  field
    ⦃ ≲-eff   ⦄ : Δ₁ ≲ Δ₂
    ⦃ ≲ᴴ-eff  ⦄ : H₁ ≲ᴴ H₂
    preserves-cases
      : ∀ {M} (m : ⟦ H₁ ⟧ᴴ M A)
      → (e′ : ∀[ M ⇒ Free Δ₂ ])
      →     □⟨ e₁ ⟩ .alg (map-sigᴴ (λ {x} → e′ {x}) m)
         ≡  extract e₂ .alg (map-sigᴴ (λ {x} → e′ {x}) (injᴴ {X = A} m))
\end{code}

\begin{code}
Correctᴴ : Theoryᴴ H → Theory Δ → □ (Elaboration H) Δ → Set₁
Correctᴴ Th T e =
  ∀ {Δ′ H′}
  → (e′ : □ (Elaboration H′) Δ′)
  → ⦃ ζ : e ⊑ e′ ⦄
  → {eq : ■ Equationᴴ _}
  → eq ◄ᴴ Th
  → Respectsᴴ (_≈⟨ T ⟩_) (extract e′) ■⟨ eq ⟩
\end{code}     

\begin{code}
compose-elab  :  ⦃ Δ₁ ∙ Δ₂ ≈ Δ ⦄
              →  □ (Elaboration H₁) Δ₁
              →  □ (Elaboration H₂) Δ₂
              →  □ (Elaboration (H₁ ∔ H₂)) Δ
□⟨ compose-elab e₁ e₂ ⟩ ⦃ w ⦄ = □⟨ e₁ ⟩ ⦃ ≲-trans ≲-∙-left w ⦄ ⋎ □⟨ e₂ ⟩ ⦃ ≲-trans ≲-∙-right w ⦄
\end{code}
\begin{code}[hide]
postulate 
\end{code}
\begin{code}
  compose-elab-correct  :  ⦃ _ : Δ₁ ∙ Δ₂ ≈ Δ ⦄ 
                        →  (e₁ : □ (Elaboration H₁) Δ₁)
                        →  (e₂ : □ (Elaboration H₂) Δ₂)
                        →  (T₁ : Theory Δ₁)
                        →  (T₂ : Theory Δ₂)
                        →  (Th₁ : Theoryᴴ H₁)
                        →  (Th₂ : Theoryᴴ H₂)
                        →  Correctᴴ Th₁ T₁ e₁
                        →  Correctᴴ Th₂ T₂ e₂ 
                        →  Correctᴴ (Th₁ [+]ᴴ Th₂) (compose-theory T₁ T₂)
                             (compose-elab e₁ e₂)
\end{code} 

\subsection{Examples}

\todo{What is a good example? Ideally, we show proof of a law that (1) is not a
  direct correspondence with the algebraic effect we elaborate into, but
  simultaneously does use an equation of the underlying theory. There are some
  candidate laws for the ``local'' operation that satisfy this.  }


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
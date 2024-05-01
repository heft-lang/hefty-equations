g\begin{code}[hide]
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
open import Data.Maybe using (maybe′)
open import Data.Bool using (true ; false ; Bool)

open import Level renaming (suc to sℓ)

open import Function.Construct.Identity
open import Function.Construct.Composition

open FreeModule renaming (_𝓑_ to bindF) hiding (_>>_)
open HeftyModule renaming (_𝓑_ to bindH) hiding (_>>_; m; n; catch)

open Abbreviation
open _∙_≈_ 

private variable M : Set → Set

open Universe ⦃ ... ⦄

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

A key aspect of algebraic effects and handlers is the ability to state and prove
equational \emph{laws} that characterize correct implementations of effectful
operations. Usually, an effect comes equipped with multiple laws that govern its
intended behavior, which altogether we refer to a as a \emph{theory} of that
effect. The concept of effect theories extends to \emph{higher-order effect
  theories}, which describe the intended behavior of higher-order effects. In
this section, we discuss how to define theories for algebraic effects in Agda by
adapting the exposition of \cite{DBLP:journals/pacmpl/YangW21}, and show how
correctness of implementations with respect to a given theory can be stated and
proved. We extend this reasoning infrastructure to higher-order effects,
allowing for modular reasoning about the correctness of elaborations of
higher-order effects.

Let us consider the state effect as an example, which comprises the $\af{get}$
and $\af{put}$ operations. With the state effect, we typically associate a set
of equations (or laws) that specify how its implementations ought to behave. One
such law is the \emph{get-get} law, which captures the intuition that the state
returned by two subsequent $\af{get}$ operation does not change if we do not use
the $\af{put}$ operation in between:
%
\begin{equation*}
  \af{‵get}\ 𝓑\ λ s →\ \af{‵get}\ 𝓑\ λ s′ →\ k\ s\ s′\ \equiv\ \af{‵get}\ 𝓑\ λ s →\ k\ s\ s
\end{equation*}
%
In a similar fashion, we an also define equational laws for higher-order
effects. For example, the following \emph{catch-return} law is usually
associated with the $\af{‵catch}$ operation of the $\af{Catch}$ effect, stating
that catching exceptions in a computation that only returns a value does
nothing.  
%
\begin{equation*}
  \af{‵catch}~(\ac{pure}~\ab{x})~\ab{m}\ \equiv\ \ac{pure}~\ab{x}
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

Effect theories are known to be closed under the co-product of effects, by
combining the equations into a new theory that contains all equations for both
effects~\citep{DBLP:journals/tcs/HylandPP06}. Similarly, theories of
higher-order effects too are closed under sums of higher-order effect
signatures. In \cref{sec:elaboration-correctness}, we show that composing two
elaborations preserves their correctness, with respect to the sum of their
respective theories. 

\subsection{Theories of Algebraic Effects}

Theories of effects are collections of equations, so we start defining the type
of equations in Agda. At its core, an equation for an effect $Δ$ is given by a
pair of effect trees of type $\ad{Free}~\ab{Δ}~A$, that define the left-hand
respectively right-hand side of the equation. However, looking at the
\emph{get-get} law above, we see that this equation contains a \emph{term
  metavariable}, i.e., $\ab{k}$. Furthermore, when considering the type of
$\ab{k}$, which is $\ab{S}~\to~\ab{S}~\to~\ad{Free}~\ab{Δ}~\ab{A}$, we see that
it refers to a \emph{type metavariable}, i.e., $\ab{A}$. Generally speaking, an
equation may refer to any number of term metavariables, which, in turn, may
depend on any number of type metavariables. Moreover, the type of the value
returned by the left hand side and right hand side of an equation may depend on
these type metavariables as well, as is the case for the \emph{get-get} law
above. This motivates the following definition of equations in Agda. 
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
$\aF{R}$ define the term metavariables respectively return type of the
equation. Both may depend on the type metavariables of the equation, hence they
depend on a vector of length $\aF{V}$ containing unapplied substitutions for all
type metavariables. Finally, the left-hand side ($\aF{lhs}$) and right-hand side
($\aF{rhs}$) of the equation are then defined as functions of type
$\ad{Free}~\ab{Δ}~(\aF{R}~vs)$, which depend on unapplied substitutions for both
the type and term level metavariables that the equation can refer to.

\paragraph*{Example}.  To illustrate how the \ad{Equation} record captures
equational laws of effects, we consider how to define the \emph{get-get} as a
value of type $\ad{Equation}~\af{State}$. Recall that the equation depends on
one type metavariable, and one term metavariable. Furthermore, the return type
of the programs on the left and right hand sides should be equal to this type
metavariable.
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
this metavariable. For equations with more than one metavariable, we would
define $\aF{Γ}$ as a product of the types of all term metavariables. The fields
$\aF{lhs}$ and $\aF{rhs}$ for the \emph{get-get} law are then defined as
follows:
%
\begin{code} 
lhs  get-get (A ∷ []) k = ‵get 𝓑 λ s → ‵get 𝓑 λ s′ → k s s′ 
rhs  get-get (A ∷ []) k = ‵get 𝓑 λ s → k s s
\end{code}
\end{AgdaAlign}

\subsection{Modal Necessity}
\label{sec:modal-necessity}

The current definition of equations is too weak, in the sense that it does not
apply in many situations where it should. The issue is that it fixes the set of
effects that can be used in the left-hand and right-hand side. To illustrate why
this is problematic, consider the following equality:
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

Given an equation for the effect $Δ$, the solution to this problem is to view
$Δ$ as a \emph{lower bound} on the effects that might occur in the left-hand and
right-hand side of the equation, rather than an exact
specification. Effectively, this means that we close over all posible contexts
of effects in which the equation can occur. This ``pattern'' of closing over all
possible extensions of a type index is
well-known~\citep{DBLP:journals/jfp/AllaisACMM21,
  DBLP:journals/pacmpl/RestPRVM22}, and corresponds to a shallow embedding of
the Kripke semantics of the necessity modality from modal logic. We can define
it in Agda as follows.
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
Intuitively, the $□$ modality transforms, for any effect-indexed type, an
\emph{exact} specification of the set of effects to a \emph{lower bound} on the
set of effects. For equations, the difference between terms of type
$\ad{Equation}~\ab{Δ}$ and $\ad{□}~\ad{Equation}~\ab{Δ}$ amounts to the former
defining an equation relating programs that have exactly effects $Δ$, while the
latter defines an equation relating programs that have at least the effects $Δ$
but potentially more. The $\ad{□}$ modality is a comonad; the counit witnesses
that we can always transform a lower bound on effects to an exact specification,
by instantiating the extension witness with a proof of reflexivity.
%
\begin{code}
extract : {P : Effect → Set₁} → □ P Δ → P Δ
extract px = □⟨ px ⟩ ⦃ ≲-refl ⦄
\end{code}

We can now redefine the \emph{get-get} law such that it applies to all programs
that have the $\ad{State}$ effect, but potentially other effects too.
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
The above definition of the \emph{get-get} law now actually does allow us to
prove the equality in \cref{eq:get-get-throw}; the term metavariable $k$ ranges
ranges over all continuations that return a tree of type
$\ad{Free}\ \ab{Δ′}\ \ab{A}$, for all $\ab{Δ′}$ such that
$\af{State}~\ad{≲}~\ab{Δ′}$. This way, we can instantiate $\ab{Δ′}$ with an
effect signature that subsumes both the $\af{State}$ and the $\af{Throw}$, which
in turn allows us to instantiate $k$ with $\af{throw}$.

\subsection{Effect Theories}

Equations for an effect $Δ$ can be combined into a \emph{theory} for $Δ$. A
theory for the effect $Δ$ is simply a collection of equations, transformed using
the $\ad{□}$ modality to ensure that term metavariables can range over programs
that include more effects than just $Δ$. 
%
\begin{code}
record Theory (Δ : Effect) : Set₁ where
  field
    arity      : Set 
    equations  : arity → □ Equation Δ
\end{code}
%
An effect theory consists of an \aF{arity}, that defines the number of equations
in the theory, and a function that maps arities to equations. We can think of
effect theories as defining a specification for how implementations of an effect
ought to behave. Although implementations may vary, depending for example on
whether they are tailored to readability or efficiency, they should at least
respect the equations of the theory of the effect they implement. We will make
precise what it means for an implementation to respect an equation in
\cref{sec:handler-correctness}.

Effect theories are closed under several composition operations that allow us to
combine the equations of different theories into single theory. The most basic
way of combining effect theories is by summing their arities.
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
theories we are combining are theories for the exact same effect. It is more
likely, however, that we would want to combine theories for different
effects. This requires that we can \emph{weaken} effect theories with respect to
the $\_≲\_$ relation. 
%
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
as witnessed by the $\af{♯}$ operation implies that it too is a such a functor.

With weakening for theories at our disposal, we can combine effect theories for
different effects into a theory of the coproduct of their respective effects.
This requires us to first define appropriate witnesses relating coproducts to
effect inclusion. 
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
It is now straightforward to show that effect theories are closed under the
coproduct of effect signatures, by summing the weakened theories.
%
\begin{code}
_[+]_ : Theory Δ₁ → Theory Δ₂ → Theory (Δ₁ ⊕ Δ₂)
T₁ [+] T₂ = weaken-theory ⦃ ≲-⊕-left ⦄ T₁ ⟨+⟩ weaken-theory ⦃ ≲-⊕-right ⦄ T₂
\end{code}
%
While this operation is in principle sufficient for our purposes, it forces a
specific order on the effects combined theories. We can further generalize the
operation above to allow for the effects of the combined theory to appear in any
order. This requires the following instances. 
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
We show that effect theories are closed under coproducts up to reordering by,
again, summing the weakened theories.
%
\begin{code}
compose-theory : ⦃ Δ₁ ∙ Δ₂ ≈ Δ ⦄ → Theory Δ₁ → Theory Δ₂ → Theory Δ
compose-theory T₁ T₂
  = weaken-theory ⦃ ≲-∙-left ⦄ T₁ ⟨+⟩ weaken-theory ⦃ ≲-∙-right ⦄ T₂ 
\end{code}
%
Since equations are defined by storing the syntax trees that define their
left-hand and right-hand side, and effect trees are weakenable, we would expect
equations to be weakenable too. Indeed, we can define the following function
witnessing weakenability of equations.
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
This begs the question: why would we opt to use weakenability of the
$□$ modality (or, bother with the
$□$ modality at all) to show that theories are weakenable, rather than using
$\af{weaken-eq}$ directly? Although the latter approach would indeed allow us to
define the composition operations for effect theories defined above, the
possible ways in which we can instantiate term metavariables remains too
restrictive. That is, we still would not be able to prove the equality in
\cref{eq:get-get-throw}, despite the fact that we can weaken the \emph{get-get}
law so that it applies to programs that use the
$\ad{Throw}$ effect as well. Instantiations of the term metavariable
$k$ will be limited to weakened effect trees, precluding any instantiation that
use operations of effects other than $\ad{State}$, such as $\af{throw}$.

Finally, we define the following predicate to witness that an equation is part
of a theory.
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
We construct a proof $\ab{eq}~\af{◄}~\ab{T}$ that an equation $\ab{eq}$ is part
of a theory $\ab{T}$ by providing an arity together with a proof that $\ab{T}$
maps to $\ab{eq}$ for that arity.

%% Finally, we must define what it means for a theory to be included in a bigger
%% theory. Given two theories, $\ab{T₁}$ and $\ab{T₂}$, ranging over effects
%% $\ab{Δ₁}$ and $\ab{Δ₂}$ respectively, we say that $\ab{T₁}$ is a
%% \emph{sub-theory} of $\ab{T₂}$ if (1) $Δ₁$ is a sub-effect of $Δ₂$, and all
%% equations of $\ab{T₁}$ are, in their weakened form, also part of $\ab{T₂}$. The
%% following record type captures this definition of sub-theories in Agda:
%% \todo{UPDATE!}
%% %
%% Here, the field $\aF{ext}$ witnesses that the effects of $\ab{T₁}$ are included
%% in the effects of $\ab{T₂}$, while the $\aF{sub}$ field transforms proofs that
%% an equation is included in $\ab{T₁}$ into a proof that its weakened form is
%% included in $\ab{T₂}$. 
%% 
\subsection{Syntactic Equivalence of Effectful Programs}
\label{sec:fo-equivalence} 

As discussed, propositional equality of effectful programs is too strict, as it
precludes us from proving equalities that rely on a semantic understanding of
the effects involved, such as the equality in \cref{eq:get-get-throw}. The
solution is to define an inductive relation that captures syntactic equivalence
modulo some effect theory. We base our definition of syntactic equality of
effectful programs on the relation defining equivalent computations by
\cite{DBLP:journals/pacmpl/YangW21}, Definition 3.1, adapting their definition
where necessary to account for the use of modal necessity in the definition of
$\ad{Theory}$. 
%
\begin{AgdaAlign}
\begin{code}
data _≈⟨_⟩_ {Δ Δ′} ⦃ _ : Δ ≲ Δ′ ⦄
  : (m₁ : Free Δ′ A) → Theory Δ → (m₂ : Free Δ′ A) → Set₁ where 
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
Since the equations of a theory are wrapped in the $\ad{□}$ modality, we cannot
refer to its components directly, but we must first provide a suitable extension
witness.

%% Fundamentally, the $\ac{≈-eq}$ constructor equates the left hand side and right
%% hand side of any given equation. Due to the use of the $\ad{□}$ modality, when
%% proving equality with respect to a theory $T₂$ we can actually use equations of
%% any sub-theory $T₁$ to prove equality. The extension witness stored in the
%% sub-theory proof $\ab{sub}$ is used to close the equation $\ab{eq}$, allowing us
%% to prove equality of its left and right hand side with respect to any larger
%% theory that includes that equation.
%% 
The $\ac{≈-eq}$ lets us sequence the left and right hand sides of an
equation with an arbitrary continuation $\ab{k}$. 
\begin{code}[hide]
postulate 𝓑-idʳ-≈ : {T : Theory Δ} → ⦃ _ : Δ ≲ Δ′ ⦄ → (m : Free Δ′ A) → m ≈⟨ T ⟩ (m 𝓑 pure) 
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
use-equation eq px vs {γ} = ≈-trans (𝓑-idʳ-≈ _) (≈-trans (≈-eq eq px vs γ pure) (≈-sym $ 𝓑-idʳ-≈ _))
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

from-≡ : ∀ {T : Theory Δ} {m₁ m₂ : Free Δ′ A} → ⦃ _ : Δ ≲ Δ′ ⦄ → m₁ ≡ m₂ → m₁ ≈⟨ T ⟩ m₂
from-≡ refl = ≈-refl 
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
  →  (‵get 𝓑 λ s → ‵get 𝓑 λ s′ → ‵throw {A = A})
     ≈⟨ StateTheory ⟩ (‵get 𝓑  λ s → ‵throw)
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
\begin{code}[hide]
module _ ⦃ _ : Universe ⦄ where 
\end{code}
\begin{code}
  data Kind : Set where set type : Kind 

  TypeContext : List Kind → Set₁
  TypeContext []            = Level.Lift _ ⊤
  TypeContext (set   ∷ vs)  = Set × TypeContext vs
  TypeContext (type  ∷ vs)  = Level.Lift (sℓ 0ℓ) Type × TypeContext vs

  record Equationᴴ (H : Effectᴴ) : Set₁ where
    field
      V        : List Kind 
      Γ        : TypeContext V → Set
      R        : TypeContext V → Set 
      lhs rhs  : (vs : TypeContext V) → Γ vs → Hefty H (R vs)
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
To illustrate: we can define the \emph{catch-return} law from the introduction of
this section as a value of type $\ad{■}~\ad{Equationᴴ}~\af{Catch}$ a
follows:~\footnote{For simplicities sake, we gloss over the use of type
  universes to avoid size issues here.}\todo{UPDATE: quantification over types
  and sets} 
%
\begin{code}[hide]
  open ■
  open Equationᴴ 

\end{code}
\begin{code} 
  catch-return : ■ Equationᴴ Catch
  V    ■⟨ catch-return ⟩               = type ∷ []
  Γ    ■⟨ catch-return ⟩ (lift t , _)  = ⟦ t ⟧ᵀ × Hefty _ ⟦ t ⟧ᵀ
  R    ■⟨ catch-return ⟩ (lift t , _)  = ⟦ t ⟧ᵀ
  lhs  ■⟨ catch-return ⟩ _ (x , m)     = ‵catch (pure x) m
  rhs  ■⟨ catch-return ⟩ _ (x , m)     = pure x
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
                 →  (vs : TypeContext (V ■⟨ eq ⟩))
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
                   →  (vs : TypeContext (V ■⟨ eq ⟩))
                   →  {γ : Γ (■⟨ eq ⟩) vs}
                   →  lhs (■⟨ eq ⟩) vs γ ≅⟨ T ⟩ rhs (■⟨ eq ⟩) vs γ  

  CatchTheory : Theoryᴴ Catch
  arity CatchTheory = ⊤
  equations CatchTheory tt = catch-return
\end{code}
%
To illustrate, we can prove that the programs
$\af{catch}~\af{throw}~(\af{censor}~\ab{f}~\ab{m})$ and
$\af{censor}~\ab{f}~\ab{m}$ are equal under a theory for the $af{Catch}$ effect
that contains the \emph{catch-return} law.
%
\begin{code}[hide]
  data CensorOp◂ : Set where censor◂ : Type → (String → String) → CensorOp◂ 

  Censor◂ : Effectᴴ
  Effectᴴ.Opᴴ Censor◂ = CensorOp◂
  Effectᴴ.Retᴴ Censor◂ (censor◂ t _) = ⟦ t ⟧ᵀ
  Effectᴴ.Fork Censor◂ (censor◂ t x) = ⊤
  Effectᴴ.Ty Censor◂ {censor◂ t _} ψ = ⟦ t ⟧ᵀ
  
  ‵censor : ∀ {t : Type} → ⦃ Censor◂ ≲ᴴ H ⦄ → (String → String) → Hefty H ⟦ t ⟧ᵀ → Hefty H ⟦ t ⟧ᵀ
  ‵censor {H = H} {t = t} f m = impure (injᴴ {M = Hefty H} ((censor◂ t f) , pure , λ where tt → m)) 
\end{code}
\begin{code}
  catch-return-censor :  ∀  {t : Type} {f} {x : ⟦ t ⟧ᵀ} {m : Hefty H ⟦ t ⟧ᵀ}
                        →  ⦃ _ : Catch ≲ᴴ H ⦄ → ⦃ _ : Censor◂ ≲ᴴ H ⦄
                        →  ‵catch (pure x) (‵censor f m)
                           ≅⟨ CatchTheory ⟩ pure x 
  catch-return-censor {f = f} {x = x} {m = m} =
    begin
      ‵catch (pure x) (‵censor f m)
    ≅⟪ use-equationᴴ catch-return (tt , refl) _ ⟫
      pure x
    ∎
    where open ≅-Reasoning _
\end{code}
%
The equivalence proof above makes, again, essential use of modal necessity. That
is, by closing over all possible extensions of the $\af{Catch}$ effe, the term
metavariable in the \emph{catch-return} law to range over programs that have
higher-order effects other than $\af{Catch}$, which is needed to apply the law
if the second branch of the $\af{catch}$ operation contains the $\af{censor}$
operation.

\subsection{Correctness of Elaborations}
\label{sec:elaboration-correctness}

As the first step towards defining correctness of elaborations, we must specify
what it means for an algebra over a higher-order effect signature $\ab{H}$ to
respect an equation. The definition is broadly similar to its counterpart for
first-order effects in \cref{sec:handler-correctness}, with the crucial
difference that the notion of begin equation respecting for higher-order effects
is parameterized over a binary relation $\ab{\_≈\_}$ between first-order effect
trees. In practice, this binary relation will be instantiated with the inductive
equivalence relation defined in \cref{sec:fo-equivalence}; propositional
equality would be too restrictive, since that preclude us from equating programs
using equations of the first-order effect(s) that we elaborate into. 
%
\begin{code}
  Respectsᴴ  : (_≈_ : ∀ {A} → Free Δ A → Free Δ A → Set₁)
             → Algᴴ H (Free Δ) → Equationᴴ H → Set₁
  Respectsᴴ _≈_ alg eq =
    ∀ {vs γ} → cataᴴ pure alg (lhs eq vs γ) ≈ cataᴴ pure alg (rhs eq vs γ)
\end{code}

Since elaborations are composed in parallel, the use of necessity in the
defintion of equations has additional consequences for their definiton of
correctness. That is, correctness of an elaboration is defined with a theory
whose equations have left-hand and right-hand sides that may contain term
metavariables that range over programs with more effects than those the
elaboration is defined for. Therefore, to state correctness, we must also close
over all possible ways these additional effects are elaborated. For this, we
define the following binary relation on extensible elaborations. 
%
\begin{code}[hide]
  open Algᴴ
\end{code}
\begin{code}
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
%
A proof of the form $\ab{e₁}~⊑~\ab{e₂}$ witnesses that the elaboration
$\ab{e₁}$ is included in $\ab{e₂}$, meaning that $\ab{e₂}$ may elaborate a
bigger set of higher-order effects, for which it may need to refer to more
first-order effects, but for those higher-order effects that are elaborated by
both $\ab{e₁}$ and $\ab{e₂}$ they should produce the same result.

We then define correctness of elaborations as follows. 
%
\begin{code}
  Correctᴴ : Theoryᴴ H → Theory Δ → □ (Elaboration H) Δ → Set₁
  Correctᴴ Th T e =
    ∀ {Δ′ H′}
    → (e′ : □ (Elaboration H′) Δ′)
    → ⦃ _ : e ⊑ e′ ⦄
    → {eq : ■ Equationᴴ _}
    → eq ◄ᴴ Th
    → Respectsᴴ (_≈⟨ T ⟩_) (extract e′) ■⟨ eq ⟩
\end{code}
%
Which is to say that an elaboration is correct with respect to a theory of the
higher-order effects it elaborates and a theory of the first-order effects it
elaborates into, if all possible extensions of the elaboration respect all
equations of the higher-order theory with respect to equivalence modulo the
first-order theory.

Crucially, correctness of elaborations is preserved under their
composition. \cref{fig:correctness-composition} shows the type of the
corresponding correctness theorem in Agda; for the full details of the proof we
refer to the Agda formalization accompanying this paper~\citep{artifact}. We
remark that correctness of a composed elaboration is defined with respect to the
composition of the theories of the first-order effects that the respective
elaborations use. Constructing a handler that is correct with respect to this
composed first-order effect theory is a separate concern; a solution based on
\emph{fusion} is detailed in the work by \cite{DBLP:journals/pacmpl/YangW21}.

\begin{code}[hide]
  compose-elab  :  ⦃ Δ₁ ∙ Δ₂ ≈ Δ ⦄
                →  □ (Elaboration H₁) Δ₁
                →  □ (Elaboration H₂) Δ₂
                →  □ (Elaboration (H₁ ∔ H₂)) Δ
  □⟨ compose-elab e₁ e₂ ⟩ ⦃ w ⦄ = □⟨ e₁ ⟩ ⦃ ≲-trans ≲-∙-left w ⦄ ⋎ □⟨ e₂ ⟩ ⦃ ≲-trans ≲-∙-right w ⦄
\end{code}

\begin{figure}
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
\caption{The central correctness theorem, which establishes that correctness of
  elaborations is preserved under composition.}
\label{fig:correctness-composition}
\end{figure}

\subsection{Example Correctness Proof}

To illustrate how the reasoning infrastructure build up in this section, we show
how to verify the \emph{catch-return} law for the elaboration $\af{eCatch}$
defined in \cref{sec:hefty-algebras}. First, we define the following syntax for
invoking a known elaboration. 
%
\begin{code}
  module Elab (e : □ (Elaboration H) Δ) where  
    ℰ⟦_⟧ : Hefty H A → Free Δ A
    ℰ⟦ m ⟧ = elaborate (extract e) m
\end{code}
%
When opening the module $\ab{Elab}$, we can use the syntax $\af{ℰ⟦}~\ab{m}
\af{⟧}$ for elaborating $m$ with some known elaboration, which helps to simplify
equational proofs for higher-order effects. 
%
\begin{code}[hide] 
  open _⊑_ 
  eCatch◂ : □ (Elaboration Catch) Throw
  □⟨ eCatch◂ ⟩ = ElabModule.eCatch
\end{code}

Now, to prove that $\af{eCatch}$ is correct with respect to a higher-order
theory for the $\af{Catch}$ effect containing the \emph{catch-return} law, we
must produce a proof that the programs
$\af{ℰ}~\af{‵catch}~(\aF{return}~\ab{x})~\ab{m}~\af{⟧}$ and
$\af{ℰ⟦}~\aF{return}~\af{⟧}$ are equal (in the sense of the inductive
equivalence relation defined in \cref{sec:fo-equivalence}) with respect to some
first-order theory for the $\af{Throw}$ effect. In this instance, we do not need
any equations from this underlying theory to prove the equality, but sometimes
it is necessary to invoke equations of the underlying first-order effects to
prove correctness of an elaboration.

\begin{code}
  eCatchCorrect : {T : Theory Throw} → Correctᴴ CatchTheory T eCatch◂ 
  eCatchCorrect {Δ′ = Δ′} e′ ⦃ ζ ⦄ (tt , refl) {γ = x , m} =
    begin
      ℰ⟦ ‵catch (pure x) m ⟧
    ≈⟪ from-≡ (sym $ ζ .preserves-cases _ ℰ⟦_⟧) ⟫
      (♯◂ (given hThrow handle (pure x) $ tt)) 𝓑 maybe′ pure (ℰ⟦ m ⟧)
    ≈⟪⟫ {- By definition of hThrow -}  
      (pure (just x) 𝓑 maybe′ pure ((ℰ⟦ m ⟧ 𝓑 pure))) 
    ≈⟪⟫ {- By definition of 𝓑 -} 
      ℰ⟦ pure x ⟧
    ∎
    where
      open ≈-Reasoning _
      open Elab e′
\end{code}
\begin{code}[hide]
      postulate instance foo : ζ .≲-eff .proj₁ ≲ Δ′
      ♯◂ = ♯_ ⦃ foo ⦄

\end{code}
%
In the Agda formalization accompanying this paper~\citep{artifact}, we verify
correctness of elaborations for the higher-order operations defined in the 3MT
library by \cite{delaware2013modular}. \cref{tab:laws} shows an overview of
first-order and higher-order effects included in the development, and the laws
which we prove about their handlers respectively elaborations.

% Please add the following required packages to your document preamble:
% \usepackage{multirow}
\begin{table}[]
\resizebox{\columnwidth}{!}{%
\begin{tabular}{c|cl}
\textbf{Effect}                    & \multicolumn{2}{l}{\textbf{Laws}}                \\ \hline\hline
\af{Throw}                         & \multicolumn{1}{c|}{$\af{‵throw}~\af{𝓑}~\ab{k}\ \equiv\ \ab{k}$} & \textit{bind-throw}      \\ \hline\hline
\multirow{4}{*}{\af{State}}        & \multicolumn{1}{c|}{$\af{‵get}~\af{𝓑}~λ~\ab{s}~→~\af{‵get}~𝓑~\ab{k}~\ab{s}\ \equiv\ \af{‵get}~𝓑~\ab{k}~\ab{s}~\ab{s}$} & \textit{get-get}         \\ \cline{2-3} 
                                   & \multicolumn{1}{c|}{$\af{‵get}~\af{𝓑}~\af{‵put}\ \equiv\ \ac{pure}~\ab{x}$} & \textit{get-put}         \\ \cline{2-3} 
                                   & \multicolumn{1}{c|}{$\af{‵put}~\ab{s}~\af{≫}~\af{‵get}\ \equiv\ \af{‵put}~\ab{s}~\af{≫}~\ac{pure}~\ab{s}$} & \textit{put-get}         \\ \cline{2-3} 
                                   & \multicolumn{1}{c|}{$\af{`put}~\ab{s}~\af{≫}~\af{‵put}~\ab{s′}\ \equiv\ \af{‵put}~\ab{s′}$} & \textit{put-put}         \\ \hline\hline
\multirow{3}{*}{\af{Reader}}       & \multicolumn{1}{c|}{$\af{‵ask}~\af{≫}~\ab{m}\ \equiv\ \ab{m}$} & \textit{ask-query}       \\ \cline{2-3} 
                                   & \multicolumn{1}{c|}{$\af{‵ask}~\af{𝓑}~λ~\ab{r}~→~\af{‵ask}~\af{𝓑}~\ab{k}~\ab{r}\ \equiv\ \af{‵ask}~\af{𝓑}~λ~\ab{r}~→~\ab{k}~\ab{r}~\ab{r}$} & \textit{ask-ask}         \\ \cline{2-3} 
                                   & \multicolumn{1}{c|}{$\ab{m}~\af{𝓑}~λ~\ab{x}~→~\af{‵ask}~\af{𝓑}~λ~\ab{r}~→~\ab{k}~\ab{x}~\ab{r}\ \equiv\ \af{‵ask}~\af{𝓑}~λ~\ab{r}~→~\ab{m}~\af{𝓑}~λ~\ab{x}~→~\ab{k}~\ab{x}~\ab{r}$} & \textit{ask-bind}        \\ \hline\hline
\multirow{4}{*}{\af{LocalReader}}  & \multicolumn{1}{c|}{$\af{‵local}~\ab{f}~(\ac{pure}\ \ab{x})\ \equiv\ \ac{pure}\ \ab{x}$} & \textit{local-pure}    \\ \cline{2-3} 
                                   & \multicolumn{1}{c|}{$\af{‵local}~\ab{f}~(\ab{m}~\af{𝓑}~\ab{k})\ \equiv\ \af{‵local}~\ab{f}~\ab{m}~\af{𝓑}~\af{‵local}~\ab{f}~\af{∘}~\ab{k}$} & \textit{local-bind}      \\ \cline{2-3} 
                                   & \multicolumn{1}{c|}{$\af{‵local}~\af{f}~\af{‵ask}\ \equiv\ \ac{pure}~\af{∘}~\ab{f}$} & \textit{local-ask}       \\ \cline{2-3} 
                                   & \multicolumn{1}{c|}{$\af{‵local}~(\ab{f}~\af{∘}~\ab{g})~\ab{m}\ \equiv\ \af{‵local}~\ab{g}~(\af{‵local}~\ab{f}~\ab{m})$} & \textit{local-local}     \\ \hline\hline
\multirow{3}{*}{\af{Catch}}        & \multicolumn{1}{c|}{$\af{‵catch}~(\ac{pure}~\ab{x})~\ab{m}\ \equiv\ \ac{pure}~\ab{x}$} & \textit{catch-pure}    \\ \cline{2-3} 
                                   & \multicolumn{1}{c|}{$\af{‵catch}~\af{‵throw}~\ab{m}\ \equiv\ \ab{m}$} & \textit{catch-throw$_1$} \\ \cline{2-3} 
                                   & \multicolumn{1}{c|}{$\af{`catch}~\ab{m}~\af{‵throw}\ \equiv\ \ab{m}$} & \textit{catch-throw$_2$} \\ \hline\hline
\multirow{2}{*}{\af{Lambda}}       & \multicolumn{1}{c|}{$\af{‵abs}~\ab{f}~\af{𝓑}~λ~\ab{f′}~→~\af{‵app}~\ab{f′}~\ab{m}$} & \textit{beta}            \\ \cline{2-3} 
                                   & \multicolumn{1}{c|}{$\ac{pure}~\ab{f}\ \equiv\ \af{‵abs}~(λ~\ab{x}~→~\af{‵app}~\ab{f}~(\af{‵var}~\ab{x}))$} & \textit{eta}             \\ 
\end{tabular}
}
\vspace{1em}
\caption{Overview of effects, their operations, and verified laws in the Agda
  code. }
\label{tab:laws}
\end{table}

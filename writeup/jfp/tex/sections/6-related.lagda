\begin{code}[hide]

module tex.sections.6-related where

open import Function
open import Data.Nat
open import Data.Product
open import Relation.Unary

variable A B : Set

\end{code}

\section{Related Work}
\label{sec:related}

As stated in the introduction of this paper, defining abstractions for
programming constructs with side effects is a research question with a long and
rich history, which we briefly summarize here.  \citet{Moggi89a} introduced
monads as a means of modeling side effects and structuring programs with side
effects; an idea which \citet{Wadler92} helped popularize.  A problem with
monads is that they do not naturally compose.  A range of different solutions
have been developed to address this
issue~\citep{Steele94,jones93,DBLP:conf/popl/Filinski99,cenciarelli1993syntactic}.
Of these solutions, monad
transformers~\citep{cenciarelli1993syntactic,Liang1995monad,DBLP:conf/ifl/Jaskelioff08}
is the more widely adopted solution.  However, more recently, algebraic
effects~\citep{Plotkin2002notions} was proposed as an alternative solution which
offers some modularity benefits over monads and monad transformers.  In
particular, whereas monads and monad transformers may ``leak'' information about
the implementation of operations, algebraic effects enforce a strict separation
between the interface and implementation of operations.  Furthermore, monad
transformers commonly require glue code to ``lift'' operations between layers of
monad transformer stacks.  While the latter problem is addressed by the Monatron
framework of \citet{DBLP:conf/ifl/Jaskelioff08}, algebraic effects have a simple
composition semantics that does not require intricate liftings.

However, some effects, such as exception catching, did not fit into the
framework of algebraic effects.  \emph{Effect
handlers}~\citep{Plotkin2009handlers} were introduced to address this problem.
Algebraic effects and handlers has since been gaining traction as a framework
for modeling and structuring programs with side effects in a modular way.
Several libraries have been developed based on the idea such as \emph{Handlers
in Action}~\citep{KammarLO13}, the freer monad~\citep{KiselyovI15}, or Idris'
\texttt{Effects} DSL~\citep{DBLP:conf/icfp/Brady13}; but also standalone
languages such as Eff~\citep{BauerP15}, Koka~\citep{Leijen17},
Frank~\citep{LindleyMM17}, and Effekt~\citep{BrachthauserSO20}.\footnote{A more
extensive list of applications and frameworks can be found in Jeremy Yallop's
Effects Bibliography: \url{https://github.com/yallop/effects-bibliography}}

As discussed
in~\cref{sec:modularity-problem}~and~\cref{sec:higher-order-effects}, some
modularity benefits of algebraic effects and handlers do not carry over to
higher-order effects.  Scoped effects and
handlers~\citep{WuSH14,PirogSWJ18,YangPWBS22} address this shortcoming for
\emph{scoped operations}, as we summarized in \cref{sec:scoped-effects}.  This
paper provides a different solution to the modularity problem with higher-order
effects.  Our solution is to provide modular elaborations of higher-order
effects into more primitive effects and handlers.  We can, in theory, encode any
effect in terms of algebraic effects and handlers.  However, for some effects,
the encodings may be complicated.  While the complicated encodings are hidden
behind a higher-order effect interface, complicated encodings may hinder
understanding the operational semantics of higher-order effects, and may make it
hard to verify algebraic laws about implementations of the interface.  Our
framework would also support elaborating higher-order effects into scoped
effects and handlers, which might provide benefits for verification.  We leave
this as a question to explore in future work.

Existing languages for algebraic effects and handlers, such as
Frank~\citep{LindleyMM17}, Koka~\citep{Leijen17}, or Flix~\citep{LutzeM24} offer indirect support for higher-order effects, via the encoding discussed in \cref{sec:wa1}.
As also discussed in \cref{sec:wa1}, this encoding suffers from a modularity problem.
Nevertheless, the encoding may suffice for applcations in practice.

Whereas Koka and Flix use so-called \emph{deep handlers}, Frank~\citep{LindleyMM17} uses \emph{shallow handlers}~\citep{HillerstromL18}.
The difference between shallow effect and deep effect handlers is in how continuations are typed.
A deep handler of type $\Typing{X}{Δ,Δ′} \Rightarrow \Typing{C}{Δ′}$ is typed as follows, where $\Op{op} : A \to B$ is an effect of type $Δ$:
%
\begin{equation*}
\Handler~\{~\cdots~(\Op{op}~\underbrace{v}_{A};\underbrace{k}_{B~\to~\Typing{C}{Δ′}})~\mapsto~\underbrace{c}_{\Typing{C}{Δ′}},~\cdots\}
\tag{$\ast$}
\label{eq:hdl-pretnar}
\end{equation*}
%
In contrast, shallow handlers are typed as follows:
%
\begin{equation*}
\Handler~\{~\cdots~(\Op{op}~\underbrace{v}_{A};\underbrace{k}_{B~\to~\colorbox{lightgray}{$\scriptstyle \Typing{X}{Δ,Δ′}$}})~\mapsto~\underbrace{c}_{\Typing{C}{Δ′}},~\cdots\}
\tag{$\ast$}
\label{eq:hdl-pretnar}
\end{equation*}
%
Following \citet{HillerstromL18}, shallow handlers can emulate deep handlers by always invoking their continuations in the scope of a recursive call to the handler being defined (assuming a language with recursive functions).
\citet{HillerstromL18} also shows how deep handlers can emulate shallow handlers.
As far as we are aware, shallow handlers support higher-order effects on a par with deep handlers, using the same encoding as we discussed in \cref{sec:wa1}.

A recent paper by~\citet{BergSPW21} introduced a generalization of scoped
effects that they call \emph{latent effects} which supports a broader class of
effects, including $\lambda$ abstraction.  While the framework appears powerful,
it currently lacks a denotational model, and seems to require similar weaving
glue code as scoped effects.  The solution we present in this paper does not
require weaving glue code, and is given by a modular but simple mapping onto
algebraic effects and handlers.

Another recent paper by~\citet{DBLP:journals/corr/abs-2302-01415}
presents a unified framework for describing higher-order effects,
which can be specialized to recover several instances such as Scoped
Effects~\citep{WuSH14} or Latent Effects~\citep{BergSPW21}. They
present a generic free monad generated from higher-order signatures
that coincides with the type of \ad{Hefty} trees that we present in
\cref{sec:hefty-trees-and-algebras}. Their approach relies on a
\emph{Generalized Fold} \citep{DBLP:journals/fac/BirdP99} for
describing semantics of handling operations, in contrast to the
approach in this paper, where we adopt a two-stage process of
elaboration and handling that can be expressed using the standard
folds of first-order and higher-order free monads. To explore how the
use of generalized folds versus standard folds affects the relative
expressivity of approaches to higher-order effects is a subject of
further study.

The equational framework we present in \cref{sec:modular-reasoning} is inspired
by the work of \citet{DBLP:journals/pacmpl/YangW21}.  Specifically, the notion
of higher-order effect theory we formalized in Agda is an extension of the
notion of (first-order) effect theory they use.  In closely related recent work
by \citet{KidneyYW24}, they present a formalization of first-order effect
theories in \emph{Cubical Agda}~\citep{VezzosiMA21}.  Whereas our formalization
requires extrinsic verification of the equalities of an effect theory, they use
\emph{quotient types} as provided by homotopy type
theory~\citep{DBLP:books/daglib/0046165} and cubical type
theory~\citep{DBLP:journals/mscs/AngiuliBCHHL21,DBLP:journals/flap/CohenCHM17} to
verify that handlers intrinsically respect their effect theories.  They also
present a Hoare logic for verifying pre- and post-conditions.  An interesting
question for future work is whether this logic and the framework of
\citet{KidneyYW24} could be extended to higher-order effect theories.

In other recent work, \citet{MatacheLMSWY25} developed an equational reasoning
system for scoped effects.
The work builds on previous work by \citeauthor{Staton13} on \emph{parameterized
algebraic theories}~\citep{Staton13,Staton13instances} which provide a syntactic framework for modeling computational effects with notions of locality (or, in scoped effects terminology, \emph{scope}).
\citet{MatacheLMSWY25} show that scoped effects translate into a variant of parameterized algebraic theories, and demonstrate that such theories provide algebraic characterizations of key examples from the literature on scoped effects: nondeterminism with semi-determinism, catching
exceptions, and local state.  

Whereas \citeauthor{MatacheLMSWY25} use parameterized algebraic theories as their underlying abstraction, \cref{sec:modular-reasoning} of this paper develops a notion of algebraic theory (\ad{Theoryᴴ} in \cref{sec:theories-of-higher-order-effects}) over the \emph{higher-order free monad}---i.e., a free monad construction that uses \emph{higher-order functors}, given by a suitably generalized notion of container, instead of usual plain functors and containers~\citep{Abbott2005containers}---in Agda's \ad{Set}.
The equations of our higher-order effect theories are validated by elaborations into free ordinary effect theories.
An interesting question for future work is to study the relationship between and compare the expressiveness of our proposed notion of higher-order effect theory and parameterized algebraic theories+scoped effects.

% The framework we present in \cref{sec:modular-reasoning} supports variables
% ranging over either values or computations (see, e.g., \af{catch-return} in
% \cref{sec:theories-of-higher-order-effects}).  Our framework does not explicitly
% distinguish these two kinds of variables.  We demonstrate that our approach lets
% us verify the laws of the higher-order exception catching effect
% (\cref{sec:proving-correctness-of-elaborations}), and characterize the semantics
% of composing higher-order effect theories (\cref{sec:elaboration-correctness}).
% Key to our approach is that the correctness of elaborations is with respect to
% an algebraic effect theory.  If this underlying theory encodes a scoped syntax,
% we may need parameterized algebraic effect theories \`{a} la
% \citet{MatacheLMSWY25} to properly characterize it.

As discussed in the introduction, this paper explores a formal semantics for
overloading-based definitions of higher-order effects.  We formalized this
semantics using an initial algebra semantics.  An alternative approach would
have been to use a so-called \emph{final tagless}~\citep{carette2009finally}
encoding.  That is, instead of declaring syntax as an inductive datatype, we
declare it as a record type, and program against that record.  A benefit of the
final tagless approach is that we do not have to explicitly fold over
syntax.  The idea is to program against interfaces given by record types; e.g.:
%
\begin{code}
record NumSymantics (Repr : Set → Set) : Set₁ where
  field  num : ℕ → Repr ℕ

record LamSymantics (Repr : Set → Set) : Set₁ where
  field  lam : (Repr A → Repr B) → Repr (A → B)
         app : Repr (A → B) → Repr A → Repr B

symantics-ex : ∀ {R} → NumSymantics R → LamSymantics R → R ℕ
symantics-ex n l = app (lam (λ x → x)) (num 42)
  where open NumSymantics n; open LamSymantics l
\end{code}
%
Using this final tagless encoding, the semantics of \af{symantics-ex} will be given by passing two concrete implementations of \ad{NumSymantics} and \ad{LamSymantics}.
In contrast, with the initial algebra semantics approach we use in \cref{sec:modular-reasoning}, we would define \af{symantics-ex} in terms of an inductive data type for \aF{app}, \aF{lam}, and \aF{num}; and then give its semantics by folding algebras over the abstract syntax tree.
A benefit of final tagless is that it tends to have a have a lower interpretive overhead~\citep{carette2009finally}, since it avoids the need to iterate over syntax trees.
These benefits extend to effects~\citep{Devriese19}.
On the other hand, the inductive data types of initial encodings support induction, whereas final tagless encodings generally do not.
We do not make extensive use of inductive reasoning in this paper, and we expect that it should be possible to port most of the definitions in our paper to use final tagless encodings.
Our main reason for using an initial encoding for our hefty trees and algebras is that it follows the tradition of modeling algebraic effects and handlers using initial encodings, and that we expect induction to be useful for some applications.


%% As discussed in the introduction, this paper explores a formal semantics for
%% overloading-based definitions of higher-order effects.  We formalized this
%% semantics using an initial algebra semantics.  An alternative approach would
%% have been to use a so-called \emph{final tagless}~\citet{carette2009finally}
%% encoding.  That is, instead of declaring syntax as an inductive datatype, we
%% declare it as a record type, and program against that record.  A benefit of the
%% final tagless approach is that we do not have to explicitly fold over
%% syntax---we simply have to provide implementations of the record type(s) instance
%% %
%% \begin{code}
%% record NumSymantics (Repr : Set → Set) : Set₁ where
%%   field  num : ℕ → Repr ℕ
%% 
%% record LamSymantics (Repr : Set → Set) : Set₁ where
%%   field  lam : (Repr A → Repr B) → Repr (A → B)
%%          app : Repr (A → B) → Repr A → Repr B
%% \end{code}
%% %
%% Following \citet{carette2009finally}, these records are called \ad{Symantics} because they declare the semantics of DSLs (e.g., numbers and lambdas above).
%% Programming against the record type essentially corresponds to writing in the syntax of the declared DSL.
%% For example, we can program against the interface as follows.
%% %
%% \begin{code}
%% symantics-ex : ∀[ (NumSymantics ∩ LamSymantics) ⇒ (_$ ℕ) ]
%% symantics-ex (n , l) = app (lam (λ x → x)) (num 42)
%%   where open NumSymantics n; open LamSymantics l
%% \end{code}
%% %
%% And we can implement the interfaces as follows:
%% %
%% \begin{code}[hide]
%% open LamSymantics
%% open NumSymantics
%% \end{code}
%% \begin{code}
%% SetNumSymantics : NumSymantics id
%% num  SetNumSymantics = id
%% 
%% SetLamSymantics : LamSymantics id
%% lam  SetLamSymantics  = id
%% app  SetLamSymantics  = _$_
%% \end{code}
%% %
%% Passing these instances as arguments to the \af{symantics-ex} program lets us run the programs; akin to folding over the syntax of a program.
%% 
%% The final tagless approach often yields efficient programs, because compilers can often optimize programs given by a concrete record instance.
%% These benefits extend to effects.
%% \citet{Devriese19} presents a final tagless encoding of monads in Haskell, using dictionary passing.
%% We expect that it is possible to encode modular elaborations of higher-order effects in a similar final style; i.e., by programming against records that encode a higher-order interface, and whose implementation is given by a free monad.
%% An important difference between the two approaches has to do with \emph{coherence}.
%% Final tagless encodings typically rely on the host language to check and guarantee that interface uses are \emph{coherent}---basically, that the semantics of programs is independent from type-checker internals~\citep{WinantD18}.
%% In contrast, the initial encodings we use here require users to explicitly union both syntaxes and semantics.
%% Such explicit unions essentially shift the responsibility of guaranteeing coherence from the host language to the programmer.
%% While this incurs overhead on behalf of the programmer, it also enables programmers to explicitly specify how to resolve coherence conflicts.
%% 
%% Ultimately, the goal of \cref{sec:modular-reasoning} was to explore a semantics of higher-order effects given by an overloading semantics.




Looking beyond purely functional models of semantics and effects, there are also
lines of work on modular support for side effects in operational
semantics~\citep{Plotkin04a}.  Mosses' Modular Structural Operational
Semantics~\citep{mosses2004modular} (MSOS) defines small-step rules that
implicitly propagate an open-ended set of \emph{auxiliary entities} which encode
common classes of effects, such as reading or emitting data, stateful mutation,
and even control effects~\citep{SculthorpeTM16}.  The K Framework~\citep{RosuS10}
takes a different approach but provides many of the same benefits.  These
frameworks do not encapsulate operational details but instead make it
notationally convenient to program (or specify semantics) with side-effects.


% \subsection{[TODO]}
% \label{sec:existing-effect-restrictions}
% 
% [TODO]
% 
%%% Local Variables:
%%% reftex-default-bibliography: ("../references.bib")
%%% End:





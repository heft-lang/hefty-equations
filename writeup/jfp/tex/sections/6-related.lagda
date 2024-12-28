\begin{code}[hide]

module tex.sections.6-related where

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

Although not explicitly advertised, some standalone languages, such as
Frank~\citep{LindleyMM17} and Koka~\citep{Leijen17} do have some support for
higher-order effects.  The denotational semantics of these features of these
languages is unclear.  A question for future work is whether the modular
elaborations we introduce could provide a denotational model.

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

In other recent work, \citet{LindleyMMSWY24} developed an equational reasoning
system for scoped effects.  The system is based on so-called \emph{parameterized
  algebraic theories}; i.e., effect theories with two kinds of variables: one
for values, and one for computations representing \emph{scopes}.  They
demonstrate how their framework supports key examples from the literature:
nondeterminism with semi-determinism, catching exceptions, and local state.  The
framework we present in \cref{sec:modular-reasoning} supports variables ranging
over either values or computations (see, e.g., \af{catch-return} in
\cref{sec:theories-of-higher-order-effects}).  Our framework does not explicitly
distinguish these two kinds of variables.  We demonstrate that our approach lets
us verify the laws of the higher-order exception catching effect
(\cref{sec:proving-correctness-of-elaborations}), and characterize the semantics
of composing higher-order effect theories (\cref{sec:elaboration-correctness}).
Key to our approach is that the correctness of elaborations is with respect to
an algebraic effect theory.  If this underlying theory encodes a scoped syntax,
we may need parameterized algebraic effect theories \`{a} la
\citet{LindleyMMSWY24} to properly characterize it.

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

%%% Local Variables:
%%% reftex-default-bibliography: ("../references.bib")
%%% End:





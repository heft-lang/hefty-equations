\begin{code}[hide]

module tex.sections.6-related where

\end{code}

\section{Related Work}
\label{sec:related}

As stated in the introduction of this paper, defining abstractions for programming constructs with side effects is a research question with a long and rich history, which we briefly summarize here.
\citet{Moggi89a} introduced monads as a means of modeling side effects and structuring programs with side effects; an idea which \citet{Wadler92} helped popularize.
A problem with monads is that they do not naturally compose.
A range of different solutions have been developed to address this issue~\cite{Steele94,jones93,DBLP:conf/popl/Filinski99,cenciarelli1993syntactic}.
Of these solutions, monad transformers~\cite{cenciarelli1993syntactic,Liang1995monad,DBLP:conf/ifl/Jaskelioff08} is the more widely adopted solution.
However, more recently, algebraic effects~\cite{Plotkin2002notions} was proposed as an alternative solution which offers some modularity benefits over monads and monad transformers.
In particular, whereas monads and monad transformers may ``leak'' information about the implementation of operations,
algebraic effects enforce a strict separation between the interface and implementation of operations.
Furthermore, monad transformers commonly require glue code to ``lift'' operations between layers of monad transformer stacks.
While the latter problem is addressed by the Monatron framework of \citet{DBLP:conf/ifl/Jaskelioff08}, algebraic effects have a simple composition semantics that does not require intricate liftings.

However, some effects, such as exception catching, did not fit into the framework of algebraic effects.
\emph{Effect handlers}~\cite{Plotkin2009handlers} were introduced to address this problem.
Algebraic effects and handlers has since been gaining traction as a framework for modeling and structuring programs with side effects in a modular way.
Several libraries have been developed based on the idea such as \emph{Handlers in Action}~\cite{KammarLO13}, the freer monad~\cite{KiselyovI15}, or Idris' \texttt{Effects} DSL~\cite{DBLP:conf/icfp/Brady13}; but also standalone languages such as Eff~\cite{BauerP15}, Koka~\cite{Leijen17}, Frank~\cite{LindleyMM17}, and Effekt~\cite{BrachthauserSO20}.\footnote{A more extensive list of applications and frameworks can be found in Jeremy Yallop's Effects Bibliography: \url{https://github.com/yallop/effects-bibliography}}

As discussed in~\cref{sec:modularity-problem}~and~\cref{sec:higher-order-effects}, some modularity benefits of algebraic effects and handlers do not carry over to higher-order effects.
Scoped effects and handlers~\cite{WuSH14,PirogSWJ18,YangPWBS22} address this shortcoming for \emph{scoped operations}, as we summarized in
\cref{sec:scoped-effects}.
This paper provides a different solution to the modularity problem with higher-order effects.
Our solution is to provide modular elaborations of higher-order effects into more primitive effects and handlers.
We can, in theory, encode any effect in terms of algebraic effects and handlers.
However, for some effects, the encodings may be complicated.
While the complicated encodings are hidden behind a higher-order effect interface, complicated encodings may hinder understanding the operational semantics of higher-order effects, and may make it hard to verify algebraic laws about implementations of the interface.
Our framework would also support elaborating higher-order effects into scoped effects and handlers, which might provide benefits for verification.
We leave this as a question to explore in future work.

Although not explicitly advertised, some standalone languages, such as Frank~\cite{LindleyMM17} and Koka~\cite{Leijen17} do have some support for higher-order effects.
The denotational semantics of these features of these languages is unclear.
A question for future work is whether the modular elaborations we introduce could provide a denotational model.

A recent paper by~\citet{BergSPW21} introduced a generalization of scoped effects that they call \emph{latent effects} which supports a broader class of effects, including $\lambda$ abstraction.
While the framework appears powerful, it currently lacks a denotational model, and seems to require similar weaving glue code as scoped effects.
The solution we present in this paper does not require weaving glue code, and is given by a modular but simple mapping onto algebraic effects and handlers.

Looking beyond purely functional models of semantics and effects, there are also lines of work on modular support for side effects in operational semantics~\cite{Plotkin04a}.
Mosses' Modular Structural Operational Semantics~\cite{mosses2004modular} (MSOS) defines small-step rules that implicitly propagate an open-ended set of \emph{auxiliary entities} which encode common classes of effects, such as reading or emitting data, stateful mutation, and even control effects~\cite{SculthorpeTM16}.
The K Framework~\cite{RosuS10} takes a different approach but provides many of the same benefits.
These frameworks do not encapsulate operational details but instead make it notationally convenient to program (or specify semantics) with side-effects.

%%% Local Variables:
%%% reftex-default-bibliography: ("../references.bib")
%%% End:





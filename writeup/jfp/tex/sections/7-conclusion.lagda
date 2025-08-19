\begin{code}[hide]

module tex.sections.7-conclusion where

\end{code}

\section{Conclusion}
\label{sec:conclusion}

In this paper, we presented a semantics for higher-order effects based
on \emph{overloading}, by defining higher-order effects in terms of
\emph{elaborations} to algebraic effect trees.  In this setup, we
program against an interface of higher-order effects in a way that
provides effect encapsulation. This means we can modularly change the
implementation of effects without changing programs written against
the interface, and without changing the definition of any interface
implementations. % Furthermore, the solution requires a minimal amount
% of glue code to compose language definitions.

Crucially, hefty trees and their elaborations support modular
reasoning. Equational proofs about programs with higher-order effects
inherit this modularity: they can be reused in the context of larger
programs, even if those rely on additional effects. Most
significantly, correctness proofs of elaborations are themselves
modular. As a result, correctness proofs can be lifted to proofs over
composite elaborations, something which is generally not possible for
algebraic effect handlers without appealing to fusion theorems.

While we have made use of Agda and dependent types throughout this
paper, the framework should be portable to less dependently-typed
functional languages, such as Haskell, OCaml, or Scala. An interesting
direction for future work is to explore whether the framework could
provide a denotational model for handling higher-order effects in
standalone languages with support for effect handlers.



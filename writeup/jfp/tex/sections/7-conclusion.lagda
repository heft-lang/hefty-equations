\begin{code}[hide]

module tex.sections.7-conclusion where

\end{code}

\section{Conclusion}
\label{sec:conclusion}

We have presented a new solution to the modularity problem with modeling and
programming with higher-order effects.  Our solution allows programming against
an interface of higher-order effects in a way that provides effect
encapsulation, meaning we can modularly change the implementation of effects
without changing programs written against the interface and without changing the
definition of any interface implementations.  Furthermore, the solution requires
a minimal amount of glue code to compose language definitions.

We have shown that the framework supports modular reasoning on a par with
algebraic effects and handlers, albeit with some administrative overhead.  While
we have made use of Agda and dependent types throughout this paper, the
framework should be portable to less dependently-typed functional languages,
such as Haskell, OCaml, or Scala. An interesting direction for future work is
to explore whether the framework could provide a denotational model for handling
higher-order effects in standalone languages with support for effect handlers.



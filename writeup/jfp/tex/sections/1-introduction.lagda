%%
%% Agda setup
%%

\begin{code}[hide]

module tex.sections.1-introduction where

open import Data.Unit
open import Data.String

\end{code}

\section{Introduction}
\label{sec:1-introduction}

\renewcommand{\AgdaEmptySkip}{0.5em}

Defining abstractions that support both programming with and reasoning
about side effects is a research question with a long and rich
history. The goal is to define an abstract interface of (possibly)
side-effecting operations together with equations describing their
behavior, where the interface hides operational details about the
operations and their side effects that are irrelevant for defining or
reasoning about a program. Such encapsulation makes it easy to
refactor, optimize, or even change the behavior of a program while
preserving proofs, by changing the implementation of the interface.

Monads~\citep{DBLP:conf/lics/Moggi89} have long been the preferred
solution to this research question, but they lack modularity: given
two computations defined in different monads, there is no canonical
way to combine them that is both universally applicable and preserves
modular reasoning. This presents a problem for scalability since, in
practice, programs, and therefore proofs, are developed
incrementally. \emph{Algebraic effects and
handlers}~\citep{Plotkin2002notions,Plotkin2009handlers} provide a
solution for this problem by defining a syntactic class of monads,
which permits composition of syntax, equational theories, and
proofs. Algebraic effects and handlers maintains a strict separation
of \emph{syntax} and \emph{semantics}, where programs are only syntax,
and semantics is assigned later on a per-effect basis using handlers.

Many common operations, however, cannot be expressed as syntax in this
framework. Specifically, \emph{higher-order operations} that take
computational arguments, such as exception catching or modifying
environments in the reader monad. While it is possible to express
higher-order operations by inlining handler applications within the
definition of the operation itself, this effectively relinquishes key
modularity benefits. The syntax, equational theories, and proofs of
such inlined operations do not compose.

In this paper, we propose to address this problem by appealing to an
\emph{overloading} mechanism which postpones the choice of handlers to
inline.  As we demonstrate, this approach provides a syntax and semantics of
higher-order operations with similar modularity benefits as traditional
algebraic effects; namely syntax, equational theories, and proofs that
compose.  To realize this, we use a syntactic class of monads that supports
higher-order operations (which we dub \emph{hefty trees}).  Algebras over this
syntax (\emph{hefty algebras}) let us modularly \emph{elaborate} this syntax
into standard algebraic effects and handlers.  We show that a wide variety of
higher-order operations can be defined and assigned a semantics this
way. Crucially, program definitions using hefty trees enjoy the same modularity
properties as programs defined with algebraic effects and handlers.
Specifically, they support the composition of syntax, semantics, equational
theories, and proofs. This demonstrates that overloading is not only
syntactically viable, but also supports the same modular reasoning as algebraic
effects for programs with side-effects that involve higher-order operations.

\subsection{Background: Algebraic Effects and Handlers}
\label{sec:background}

\newcommand{\Id}[1]{\mathit{#1}}
\newcommand{\Op}[1]{\mathit{#1}}
\newcommand{\Type}[1]{\mathit{#1}}
\newcommand{\Effect}[1]{\mathit{#1}}
\newcommand{\Typing}[2]{{#1}\mathop{!}{#2}}
\newcommand{\HTyping}[2]{{#1}\mathop{!\kern-1pt!}{#2}}
\newcommand{\Elabarr}{\Rrightarrow}
\newcommand{\Handler}{\mathbf{handler}}
\newcommand{\Do}{\mathbf{do}}
\newcommand{\Return}{\mathbf{return}}
\newcommand{\EmptyString}{\text{``''}}
\newcommand{\String}[1]{\text{``{#1}''}}
\newcommand{\With}[2]{\textbf{with}~{#1}~\textbf{handle}~{#2}}
\newcommand{\HWith}[2]{\textbf{with}~{#1}~\textbf{elaborate}~{#2}}
\newcommand{\Case}{\textbf{case}}
\newcommand{\If}{\textbf{if}}
\newcommand{\Then}{\textbf{then}}
\newcommand{\Else}{\textbf{else}}
\newcommand{\Let}{\textbf{let}}
\newcommand{\In}{\textbf{in}}
\newcommand{\Elaborate}{\textbf{elaborate}}
\newcommand{\Conc}{\mathrel{+\mkern-8mu+}}
\newcommand{\EDec}[1]{\mathbf{effect}~{\Effect{#1}}}

To understand the modularity benefits of algebraic effects and handlers, and why this modularity breaks when defining operations that take computations as parameters, we give a brief introduction to algebraic effects.
%Readers familiar with algebraic effects and handlers are encouraged to skim the code examples in this subsection and read its final paragraph.
To this end, we will use informal examples using a simple calculus inspired by Pretnar's calculus for algebraic effects~\citep{Pretnar15}. 
\Cref{sec:algebraic-effects} of this paper provides a semantics for algebraic effects and handlers in Agda which corresponds to this calculus.

\subsubsection{Effect Signatures}
Say we want an effectful operation $\Op{out}$ for printing output.
Besides its side-effect of printing output, the operation should take a string as an argument and return the unit value.
Using algebraic effects, we can declare this operation using the following \emph{effect signature}:
%
\begin{equation*}
  \EDec{Output} = \Op{out} : \Type{String} \to ()
\end{equation*}
%
We can use this operation in any program that that has the $\Effect{Output}$ effect.
For example, the following $\Id{hello}$ program:
%
\begin{align*}
  \Id{hello} &: \Typing{()}{\Effect{Output}}
  \\[-0.5ex]
  \Id{hello} &= \Op{out}~\String{Hello};~\Op{out}~\String{ world!}
\end{align*}
%
The type $\Typing{\Type{()}}{Output}$ indicates that $\Id{hello}$ is an effectful computation which returns a unit value, and which is allowed to call the operations in $\Effect{Output}$ (i.e., only the $\Op{out}$ operation).

More generally, computations of type $\Typing{A}{Δ}$ are allowed (but not required) to call any operation of any effect in $Δ$, where $Δ$ is a \emph{row} (i.e., unordered sequence) of effects.
An \emph{effect} is essentially a label associated with a set of operations.
The association of labels to operations is declared using effect signatures, akin to the signature for $\Effect{Output}$ above.

\subsubsection{Effect Theories}
A crucial feature of algebraic effects and handlers is that it permits abstract reasoning about programs containing effects, such as $\Id{hello}$ above.
That is, each effect is associated with a set of laws that characterizes the behavior of its operations.
Their purpose is to constrain an effect's behavior without appealing to any specifics of the implementation of the effects.
Consequently, program proofs derived from these equations remain valid for all handler implementations satisfying the laws of its equational theory.

Importantly, these laws are purely \emph{syntactic}, in the sense that they are part of the effect's specification rather than representing universal truths about the behavior of effectful computation.
Whether a law is "valid" depends entirely on how we handle the effects, and different handlers  may satisfy different laws. 
Figuring out a suitable set of laws is part of the development process of (new) effects.
Typically, the final specification of an effect is the result of a back-and-forth refinement between an effect's specification and its handler implementations.
This process ultimately converges to a definition that matches our intuitive understanding of what an effect should do.

% 
% , such as $\Id{hello}$, abstract from the concrete semantics of the $\Op{out}$ effect yet still let us reason about programs.
% Specifically, each effect is associated with a set of laws that characterize the behavior of its effectful operations.
% 

For example, the $\Effect{Output}$ effect has a single law that characterizes the behavior of $\Op{out}$:
%
\begin{equation*}
  \Op{out}~s_1; \Op{out}~s_2 \equiv \Op{out}~(s_1 \Conc s_2)
\end{equation*}
%
Here $\Conc$ is string concatenation.
Using this law, we can prove that our $\Id{hello}$ program will print the string $\String{Hello world!}$.
Crucially, this proof does not depend on operational implementation details of the $\Effect{Output}$ effect.
Instead, it uses the laws of the equational theory of the effect.
While the program and effect discussed so far has been deliberately simple, the approach illustrates how algebraic effects let us reason about effectful programs in a way that abstracts from the concrete implementation of the underlying effects.
% While many existing languages and calculi on algebraic effects gloss over the existence of these laws, they are a crucial conceptual innovation and attraction of the approach.

\subsubsection{Effect Handlers}
An alternative perspective is to view effects as interfaces that specify the parameter, return type, and laws of each operation.
Implementations of such interfaces are given by \emph{effect handlers}.
An effect handler essentially defines how to interpret operations in the execution context they occur in.
This interpretation must be consistent with the laws of the effect.
(We will not dwell further on this consistency here; we return to this in \cref{sec:handler-correctness}.)

The type of an effect handler is $\Typing{A}{Δ}~\Rightarrow~\Typing{B}{Δ′}$, where $Δ$ is the row of effects before applying the handler and $Δ′$ is the row after.
For example, here is a specific type of an effect handler for $\Effect{Output}$:\footnote{Here and throughout the rest of this paper, type variables that are not explicitly bound elsewhere are implicitly universally quantified in prenex position of the type in which they occur.}
%
\begin{equation*}
    \Id{hOut} : \Typing{A}{\Effect{Output},Δ}
                \Rightarrow
                \Typing{(A \times \Type{String})}{Δ}
\end{equation*}
%
%The type on the left of the double arrow is the computation before handling, and the type on the right is the computation after.
The $\Effect{Output}$ effect is being handled, so it is only present in the effect row on the left.\footnote{$\Effect{Output}$ could occur in the universally quantified $Δ$ too.
This raises the question: which $\Effect{Output}$ effect does a given handler actually handle?
We refer to the literature for answers to this question; see, e.g., the row treatment of \citet{morris2019abstracting}, the \emph{effect lifting} of \citet{DBLP:journals/pacmpl/BiernackiPPS18}, and the \emph{effect tunneling} of \citet{DBLP:journals/pacmpl/ZhangM19}.}
As the type suggests, this handler handles $\Op{out}$ operations by accumulating a string of output.
Below is an example implementation of this handler:
%
\begin{equation*}
  \Id{hOut} =
    \Handler~\{
      \begin{array}[t]{ll}
        (\Return~x)~\mapsto~\Return~(x, \EmptyString)
          \\
        (\Op{out}~s;k)~\mapsto
          ~\Do~(y, s')~←~k~();
          ~\Return~(y, s~\Conc~s') ~\}
      \end{array}
\end{equation*}
%
The $\Return{}$ case of the handler says that, if the computation being handled terminates normally with a value $x$, then we return a pair of $x$ and the empty string.
The case for $\Op{out}$ binds a variable $s$ for the string argument of the operation, but also a variable $k$ representing the \emph{execution context} (or \emph{continuation}).
Invoking an operation suspends the program and its execution context up-to the nearest handler of the operation.
The handler can choose to re-invoke the suspended execution context (possibly multiple times).
The handler case for $\Op{out}$ above always invokes $k$ once.
Since $k$ represents an execution context that includes the current handler, calling $k$ gives a pair of a value $y$ and a string $s′$, representing the final value and output of the execution context.
The result of handling $\Op{out}~s$ is then $y$ and the current output ($s$) plus the output of the rest of the program ($s′$).

In general, a computation $m : \Typing{A}{Δ}$ can only be run in a context that provides handlers for each effect in $Δ$.
To this end, the expression $\With{h}{m}$ represents applying the handler $h$ to handle a subset of effects of $m$.
For example, we can run the $\Id{hello}$ program from earlier with the handler $\Id{hOut}$ to compute the following result:
\begin{equation*}
  (\With{\Id{hOut}}{\Id{hello}}) \ \equiv\ ((), \String{Hello world!})
\end{equation*}

The key benefit algebraic effects and handlers is that programs such as $\Id{hello}$ are defined \emph{independently} of how the effectful operations they use are implemented.
This makes it is possible to reason about programs independently of how the underlying effects are implemented; and also makes it possible to refine, refactor, and optimize the semantics of operations, without having to modify the programs that use them.
For example, we could refine the meaning of $\Id{out}$ \emph{without modifying the $\Id{hello}$ program or proofs derived from equations of the $\Id{Output}$ effect}, by using a different handler which prints output to the console.
%The types of algebraic effects and handlers enforces the type safety of such behavioral modifications.
However, some operations are challenging to express while retaining the same modularity benefits.
%The next subsection explains the issue.


\subsection{The Modularity Problem with Higher-Order Operations}
\label{sec:modularity-problem}

% Following~\citep{Plotkin2002notions,Plotkin2009handlers}, we can think of effectful programs as abstract syntax trees, and handlers as functions that manipulate those trees.
% The abstract syntax trees that represent effectful computations have limited support for higher-order operations.

We discuss the problem with defining higher-order operations using effect signatures (\cref{sec:the-problem}), and potential workarounds (\cref{sec:wa1,sec:wa2}).


\subsubsection{The Problem}
\label{sec:the-problem}

Say we want to declare an operation $\Op{censor}\, f\, m$ which applies a censoring function $f : \Type{String} \to \Type{String}$ to the side-effectful output of the computation $m$.
We might try to declare an effect $\Op{Censor}$ with a $\Op{censor}$ operation by the following type:
%
\begin{equation*}
  \Op{censor} : (\Type{String} \to \Type{String}) \to \Typing{A}{\Effect{Censor},Δ} \to \Typing{A}{\Effect{Censor},Δ}
\end{equation*}
%
However, using algebraic effects, we cannot declare $\Op{censor}$ as an operation.

The problem is that effect signatures do not offer direct support for declaring operations with computation parameters.
Effect signatures have the following shape:
%
\begin{align*}
  \EDec{E} &= \Op{op}_1 : A_1 \to B_1 \mid \cdots \mid \Op{op}_n : A_n \to B_n
\end{align*}
%
Here, each operation parameter type $A_i$ is going to be typed as a value.
While we may pass around computations as values, passing around computations as arguments of computations is not a desirable approach to defining higher-order operations in general.
We will return to this point in \cref{sec:wa1}.

The fact that effect signatures do not directly support operations with computational arguments is also evident from how handler cases are typed~\citep[Fig.~6]{Pretnar15}:
%
\begin{equation*}
\Handler~\{~\cdots~(\Op{op}~\underbrace{v}_{A};\underbrace{k}_{B~\to~\Typing{C}{Δ′}})~\mapsto~\underbrace{c}_{\Typing{C}{Δ′}},~\cdots\}
\tag{$\ast$}
\label{eq:hdl-pretnar}
\end{equation*}
%
Here, $A$ is the argument type of an operation, and $B$ is the return type of an operation.
The term $c$ represents the code of the handler case, which must have type $C~!~Δ′$.
% The only way for $c$ to have this type is if (1) $c = \Return~{w}$, for some $w : C$; (2) if $c$ calls the continuation $k$; or (3) if the operation argument type $v$ has type  $A = () \to \Typing{C}{Δ′}$.
% Here, option (3) seems most promising for encoding higher-order effects.
%
Observe how it is only the continuation $k$ that has an effect type.


 A consequence of this observation is that we can only define and modularly handle higher-order operations whose computation parameters are \emph{continuation-like}.
Following \citet{PlotkinP03}, such operations satisfy the following law, known as the \emph{algebraicity property}.
For any operation $\Op{op} : \Typing{A}{Δ} \to \cdots \to \Typing{A}{Δ} \to \Typing{A}{Δ}$ and any $m_1,\ldots,m_n$ and $k$,
%
\begin{equation*}
  \Do~x \leftarrow (\Op{op}~m_1\ldots m_n); k~x
  \ \equiv\ 
  \Op{op}~(\Do~x \leftarrow m_1; k~x)\ldots(\Do~x \leftarrow m_n; k~x)
  \tag{$\dagger$}
  \label{eqn:algebraicity}
\end{equation*}
%
The law says that the computation parameter values $m_1,\ldots,m_n$ are only ever run in a way that \emph{directly} passes control to $k$.
Such operations can without loss of generality or modularity be encoded as operations \emph{without} computation parameters;\footnote{Concretely, we can represent the operation in question as $\Op{op}~m_1\ldots{}m_n = \Do~x \leftarrow \Op{op′}~(); \Id{select}~x$ where $\Op{op′} : () \to \Typing{D^n}{Δ}$ and $\Id{select} : D^n \to \Typing{A}{Δ}$ is a function that chooses between $n$ different computations using a data type $D^n$ whose constructors are $d_1,\ldots,d_n$ such that $\Id{select}~d_i = m_i$ for $i \in \{1,\ldots,n\}$.} i.e., as algebraic operations that match the handler typing in~(\ref{eq:hdl-pretnar}) above.

Some higher-order operations obey the algebraicity property; many do not.
Examples that do not include:
%
\begin{itemize}
\item Exception handling: let $\Op{catch}~m_1~m_2$ be an operation that handles exceptions thrown during evaluation of computation $m_1$ by running $m_2$ instead, and $\Op{throw}$ be an operation that throws an exception. These operations are not algebraic. For example,
  \[
    \Do~(\Op{catch}~m_1~m_2); \Op{throw}\ \not\equiv\
    \Op{catch}~(\Do~m_1; \Op{throw})~(\Do~m_2; \Op{throw})
  \]
\item Local binding (the \emph{reader monad}~\citep{DBLP:conf/afp/Jones95}): let $\Op{ask}$ be an operation that reads a local binding, and $\Op{local}~r~m$ be an operation that makes $r$ the current binding in computation $m$.  Observe:
  \[
    \Do~(\Op{local}~r~m); \Op{ask}
    \ \not\equiv\
    \Op{local}~r~(\Do~m; \Op{ask})
  \]
\item Logging with filtering (an extension of the \emph{writer monad}~\citep{DBLP:conf/afp/Jones95}): let $\Op{out}~s$ be an operation for logging a string, and $\Op{censor}~f~m$ be an operation for post-processing the output of computation $m$ by applying $f : \Type{String} \to \Type{String}$.\footnote{The $\Op{censor}$ operation is a variant of the function by the same name the widely used Haskell \texttt{mtl} library: \url{https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Writer-Lazy.html}}
Observe:
  \[
    \Do~(\Op{censor}~f~m); \Op{out}~s
    \ \not\equiv\
    \Op{censor}~f~(\Do~m; \Op{out}~s)
  \]
\item Function abstraction as an effect: let $\Op{abs}~x~m$ be an operation that constructs a function value binding $x$ in computation $m$, $\Op{app}~v~m$ be an operation that applies a function value $v$ to an argument computation $m$, and $\Op{var}~x$ be an operation that dereferences a bound $x$.  Observe:
  \[
    \Do~(\Op{abs}~x~m); \Op{var}~x
    \ \not\equiv\
    \Op{abs}~x~(\Do~m; \Op{var}~x)
  \]
\end{itemize}



\subsubsection{Potential Workaround: Computations as Arguments of Operations}
\label{sec:wa1}

A tempting possible workaround to the issues summarized in \cref{sec:the-problem} is to declare an effect signature with a parameter type $A_i$ that carries effectful computations.
However, this workaround can cause operations to escape their handlers.
Following~\citet{Pretnar15}, the semantics of effect handling obeys the following law.\footnote{This law concerns so-called \emph{deep handlers}.  However, the semantics of so-called \emph{shallow handlers}~\citep{LindleyMM17,HillerstromL18} exhibit similar behavior.}
If $h$ handles operations other than $\Op{op}$, then:
%
\begin{equation}
\With{h}{(\Do~x \leftarrow \Op{op}~v; k~x)}\
\equiv\
\Do~x \leftarrow \Op{op}~v; (\With{h}{k~x})
\tag{$\dagger$}
\label{eq:hdl-eq-pretnar}
\end{equation}
%
This law tells us that effects in $v$ will not be handled by $h$.
This is problematic if $h$ is the intended handler for one or more effects in $v$.
The solution we describe in \cref{sec:solving-the-modularity-problem} does not suffer from this problem.

Nevertheless, for applications where it is known exactly which effects $v$ contains, we can work around the issue by encoding computations as argument values of operations.
We consider how, and discuss the modularity problems that this workaround suffers from.
The following $\Effect{Censor}$ effect declares the type of an operation $\Op{censorOp}~(f,m)$ where $f$ is a censoring function and $m$ is a computation encoded as a value argument:\footnote{The self-reference to $\Effect{Censor}$ in the computation parameter requires type-level recursion that is challenging to express in, e.g., the Agda formalization of algebraic effects we present in \cref{sec:algebraic-effects}.  However, such type-level recursion is supported by, e.g., Frank~\citep{LindleyMM17}, Koka~\citep{Leijen17}, and in a Haskell embeddings of algebraic effects~\citep{KammarLO13,WuSH14}.}
%
\begin{equation*}
\EDec{Censor} = \Op{censorOp} : (\Type{String} \to \Type{String}) \times (\Typing{A}{\Effect{Censor},\Effect{Output}}) \to A
\end{equation*}
%
This effect can be handled as follows:
%
\begin{align*}
\arraycolsep=1pt
\Id{hCensor} &: \Typing{A}{\Effect{Censor},\Effect{Output}} \Rightarrow \Typing{A}{\Effect{Output}}
\\
\Id{hCensor} &= \Handler~\{{\begin{array}[t]{l}
  (\Op{censorOp}~(f,m); k)~\mapsto~\Do
  \\
  \quad (x, s) \leftarrow \With{\Id{hOut}}{(\With{\Id{hCensor}}{m})}
  \\
  \quad\Op{out}~(f~s)
  \\
  \quad~k~x
  \\
  (\Return{}~x)~\mapsto~\Return{}~x~\}
\end{array}}
\end{align*}
%
The handler case for $\Op{censorOp}$ runs $m$ with handlers for both the $\Effect{Output}$ and $\Effect{Censor}$ effects, which yields a pair $(x,s)$ where $x$ represents the value returned by $m$, and $s$ represents the (possibly sub-censored) output of $m$.
We then output the result of applying the censoring function $f$ to $s$, before passing $x$ to the continuation $k$.

This handler lets us run programs such as the following:
%
\begin{equation*}
  \arraycolsep=1.4pt
  \begin{array}{ll}
    \Id{censorHello} &: \Typing{()}{\Effect{Censor},\Effect{Output}}
    \\
    \Id{censorHello} &= \Op{censorOp}~((\lambda s.~ \If~(s \equiv \String{Hello})~\Then~\String{Goodbye}~\Else~s),\Id{hello})
  \end{array}
\end{equation*}
%
Applying $\Id{hCensor}$ and $\Id{hOut}$ yields the printed output $\String{Hello world!}$, because $\String{Hello world!} \not\equiv \String{Hello}$:
%
\begin{equation*}
  \With{\Id{hOut}}{(\With{\Id{hCensor}}{\Id{censorHello}})} \equiv ((), \String{Hello world!})
\end{equation*}
%

As the example above illustrates, it is sometimes possible to encode higher-order effects as algebraic operations.
However, encoding higher-order operations in this way suffers from a modularity problem.
Say we want to extend our program with a new effect for throwing exceptions---i.e., an effect with a single operation $\Op{throw}$---and a new effect for catching exceptions---i.e., an effect with a single operation $\Op{catch}~m_1~m_2$ where exceptions thrown by $m_1$ are handled by running $m_2$.
The $\Effect{Throw}$ effect is a plain algebraic effect, defined as follows.\footnote{Here $\bot$ is the empty type.}
%
\begin{align*}
\EDec{Throw} &= \Op{throw} : () \to \bot
\end{align*}
%
The $\Effect{Catch}$ effect is higher-order.
We can again encode it as an operation with computations as value arguments.
%
\begin{align*}
\arraycolsep=0.7pt
\EDec{Catch} &= \Op{catchOp} {\begin{array}[t]{l}
  : \Typing{A}{\Effect{Catch},\Effect{Throw},\Effect{Censor},\Effect{Output}}
  \\
  \times~\Typing{A}{\Effect{Catch},\Effect{Throw},\Effect{Censor},\Effect{Output}}
  \\
  \to A
  \end{array}}
\end{align*}
%
To support subcomputations with exception catching, we need to refine the computation type we use for $\Effect{Censor}$.
(This refinement could have been done modularly if we had used a more polymorphic type.)
%
\begin{align*}
\EDec{Censor} = \Op{censorOp} : (\Type{String} \to \Type{String}) \times (\Typing{A}{\Effect{Catch},\Effect{Throw},\Effect{Censor},\Effect{Output}}) \to A
\end{align*}
%
The modularity problem arises when we consider whether to handle $\Effect{Catch}$ or $\Effect{Censor}$ first.
If we handle $\Effect{Censor}$ first, then we get exactly the problem described earlier in connection with the law~(\ref{eq:hdl-eq-pretnar}): the handler $\Id{hCensor}$ is not applied to sub-computations of $\Op{catchOp}$ operations.
Let us consider the consequences of this.
Say we want to define a handler for $\Op{catchOp}$ of the following type:
%
\begin{equation*}
\Id{hCatch} : \Typing{A}{\Effect{Catch},\Effect{Throw},\Effect{Output}} \Rightarrow \Typing{A}{\Effect{Throw},\Effect{Output}}
\end{equation*}
%
Any such handler which calls the sub-computation $m_1$ of an operation $\Op{catchOp}~m_1~m_2$ must invoke a handler for the $\Effect{Censor}$ effect.
Otherwise the handler would allow effects to escape in a way that breaks the typing discipline of algebraic effects and handlers~\citep{Pretnar15}.
While for some applications it may be acceptable to write handlers that reinvoke already-applied handlers, such reinvocation is non-modular and should not be---and, indeed, is not---necessary.
Before showing the solution we propose which avoids this, we first consider a different workaround (\cref{sec:wa2}), and previous solutions proposed in the literature (\cref{sec:previous-approaches}). 


% To see the implications of this law, let us consider the following candidate effect signature for a $\Effect{Censor}$ effect parameterized by an effect type $\Delta′$ representing sub-computation effects:\footnote{The self-reference to $\Effect{Censor}$ in the computation parameter requires type-level recursion that is challenging to express in, e.g., the Agda formalization of algebraic effects we present in \cref{sec:algebraic-effects} of this paper.  However, such type-level recursion would be allowed in, e.g., Frank~\citep{LindleyMM17}, Koka~\citep{Leijen17}, or in a Haskell embedding of algebraic effects.}
% %
% \begin{equation*}
% \EDec{Censor}_{Δ′} = \Op{censor} : \forall A.\ (\Type{String} \to \Type{String}) \times \Typing{A}{\Effect{Censor}_{Δ′},Δ′} \to A
% \end{equation*}
% %
% We can handle this effect as follows:
% %


% C: changing the wording here to not inadvertently frame our contributions as a "workaround" 
\subsubsection{Potential Workaround: Define Higher-Order Operations as Handlers}
\label{sec:wa2}

It is possible to define many higher-order operations in terms of algebraic effects and handlers.
For example, instead of defining $\Op{censor}$ as an operation, we could define it as a function which uses an inline handler application of $\Id{hOut}$:
%
\begin{gather*}
  \arraycolsep=1.4pt
  \begin{array}{ll}
    \Op{censor} &: (\Type{String} \to \Type{String}) \to \Typing{A}{\Effect{Output},Δ} \to \Typing{A}{\Effect{Output},Δ}
    \\
    \Op{censor} &f~m = \Do~(x, s) \leftarrow (\With{\Id{hOut}}{m});~\Op{out}~(f~s);~\Return{}~x
  \end{array}
\end{gather*}
%
Defining higher-order operations in terms of standard algebraic effects and handlers in this way is a key use case of effect handlers~\citep{Plotkin2009handlers}.
In fact, all other higher-order operations above (with the exception of function abstraction) can be defined in a similar manner.

However, it is unclear what the semantics is of composing syntax, equational theories, and proofs of programs with such functions occuring inline in programs.
We address this gap by proposing notions of syntax and equational theories for programs with higher-order operations.
The semantics of such programs and theories is given by elaborating them into standard algebraic effects and handlers.

% First, a few remarks on previous work that addresses similar problems as us.

% Specifically, if we apply the  are not a part of any effect interface.
% So, unlike plain algebraic operations, the only way to refactor, optimize, or change the semantics of higher-order operations defined in this way is to modify or copy code.
% In other words, we forfeit one of the key attractive modularity features of algebraic effects and handlers.

\subsubsection{Previous Approaches to Solving the Modularity Problem}
\label{sec:previous-approaches}

The modularity problem of higher-order effects, summarized in \cref{sec:the-problem}, was first observed by \citet{WuSH14} who proposed \emph{scoped effects and handlers}~\citep{WuSH14,PirogSWJ18,YangPWBS22} as a solution.
Scoped effects and handlers work for a wide class of effects, including many higher-order effects, providing similar modularity benefits as algebraic effects and handlers when writing programs.
Using \emph{parameterized algebraic theories}~\citep{LindleyMMSWY24,MatacheLMSWY25} it is possible reason about programs with scoped effects independently of how their effects are implemented.

\Citet{BergSPW21} recently observed, however, that operations that defer computation, such as evaluation strategies for $\lambda$ application or \emph{(multi-)staging} \citep{TahaS00}, are beyond the expressiveness of scoped effects.
Therefore, \citet{BergSPW21} introduced another flavor of effects and handlers that they call \emph{latent effects and handlers}.
It remains an open question how to reason about latent effects and handlers independently of how effects are implemented.

In this paper, we demonstrate that an overloading-based approach provides a semantics of composition for effect theories that is comparable to standard algebraic effects and handlers, and, we expect, to parameterized algebraic theories.
Furthermore, we demonstrate that the approach lets us model the syntax and semantics of key examples from the literature: optionally transactional exception catching, akin to scoped effect handlers~\citep{WuSH14}, and evaluation strategies for effectful $\lambda$ application~\citep{BergSPW21}.
Formally relating the expressiveness of our approach with, e.g., scoped effects and parameterized algebraic theories, is future work.

% \subsubsection{Possible Solution: Encoding Computations as Operation Arguments}
% \label{sec:encoding-arguments}

% As observed at the end of \cref{sec:modularity-problem}, many higher-order operations are not algebraic.
% However, it is, in principle, possible to declare operations such that their arguments (e.g., the $v : A$ bound in the handler case \cref{eq:hdl-pretnar} above) contain computations.
% This would operations them algebraic.
% However, it does not provide a satisfactory answer to key question (1) above.

% To illustrate, let us consider the $\Op{censor}$ operation from before.
% %
% \begin{equation*}
%   \Op{censor} : (\Type{String} \to \Type{String}) \to \underbrace{\Typing{A}{\Effect{Censor},Δ}} \to \Typing{A}{\Effect{Censor},Δ}
% \end{equation*}
% %
% The question is, how do we declare the underbraced argument parameter as an operation argument, in a way that it is guaranteed to have the same effects $\Delta$ as the context that the operation occurs in?
% Due to the way that effectful operations are declared, this is not possible in general.

% One workaround is to restrict $\Op{censor}$ to have a computation argument which has a limited set of effects, such as the following operation with effects $\Effect{Censor}$ and $\Effect{Out}$; i.e.:
% %
% \begin{equation*}
%   \Op{censor} : (\Type{String} \to \Type{String}) \to \Typing{A}{\Effect{Censor},\Effect{Out}} \to \Typing{A}{\Effect{Censor},Δ}
% \end{equation*}
% %
% This operation has $\Effect{Censor},Δ$ as its return effects, where $Δ$ is an (implicitly) universally quantified variable, whereas the effects in the argument are $\Effect{Censor},\Effect{Out}$.
% The reason we have a universally quantified variable in the return type is that algebraic effect operations are declared to have 

% We can handle this effect using the $\Id{elabCensor}$ function from \cref{sec:elaborating-functions}.
% %
% \begin{align*}
% hCensorOut &: \Type{X}~!~\Effect{Censor},\Effect{Out}~\to~\Type{X}~!~\Effect{Out}
% \\
% hCensorOut &= \Handler~\{~(\Op{censor}~f~m; k)~\mapsto~\Id{elabCensor}~f~m; (\Return~{x}) \mapsto \Return~x~\}
% \end{align*}
% %
% % The following law~\citep{Pretnar15} summarizes why.
% % For any handler $h$ of operations other than $\Op{op}$:
% % %
% % \begin{equation*}
% % \With{h}{(\Do~x \leftarrow \Op{op}~v; m)}\
% % \equiv\
% % \Do~x \leftarrow \Op{op}~v; (\With{h}{m})
% % \end{equation*}
% % %
% Now, we can define programs that use the effect---provided that those programs \emph{only} use the $\Effect{Censor}$ and $\Effect{Output}$ effects.
% For example, the following program which censors and replaces the string ``Hello'' with the string ``Goodbye'':
% %
% \begin{equation*}
%   \arraycolsep=1.4pt
%   \begin{array}{ll}
%     \Id{censorHello} &: \HTyping{()}{\Effect{Censor},\Effect{Output}}
%     \\
%     \Id{censorHello} &= \Op{censor}~(\lambda s.~ \If~(s \equiv \String{Hello})~\Then~\String{Goodbye}~\Else~s)~\Id{hello}
%   \end{array}
% \end{equation*}
% %
% Handling the program gives us the intended semantics:
% %
% \begin{equation*}
%   \Id{hOut}~(\Id{hCensor}_1~\Id{censorHello}) \equiv ((), \String{Hello world!})
% \end{equation*}
% %
% However, this strategy only works if we restrict operations to carry computation arguments with a particular set of effects.

% A possible workaround is to parameterize $\Effect{Censor}$ by the set of effects that can occur in computation arguments; e.g.:
% %
% \begin{align*}
% \Op{censor}_{Δ′} &: (\Type{String} \to \Type{String}) \to \Typing{A}{\Effect{Censor}_{Δ′},Δ′} \to \Typing{A}{\Effect{Censor}_{Δ′},Δ}
% \\
% hCensor_{Δ′} &: \Type{X}~!~\Effect{Censor},Δ′~\to~\Type{X}~!~Δ′
% \\
% hCensor_{Δ′} &= \Handler~\{~(\Op{censor}~f~m; k)~\mapsto~\Id{elabCensor}~f~m; (\Return~{x}) \mapsto \Return~x~\}
% \end{align*}
% %
% However, consider what happens if we have programs with more than one higher-order effect.
% Specifically, say we want a program with an exception catching effect, $\Effect{Catch}$, with a single catch operation that we parameterize in a similar manner:
% %
% \begin{equation*}
%   \Op{catch} : \Typing{A}{\Effect{Catch}_{Δ′}, Δ′} \to \Typing{A}{\Effect{Catch}_{Δ′}, Δ′} \to \Typing{A}{\Effect{Catch}_{Δ′}, Δ}
% \end{equation*}

%  such as the following which uses both the censor effect and the higher-order catch effect:
% %
% \begin{align*}
%   \arraycolsep=1.4pt
%   \begin{array}{ll}
%     \Id{censorCatchHello} &: \HTyping{()}{\Effect{Censor}_{\Effect{Output},\Effect{Catch_{?}}},\Effect{Output},\Effect{}}
%     \\
%     \Id{censorCatchHello} &= \Op{censor}~(\lambda s.~ \If~(s \equiv \String{Hello})~\Then~\String{Goodbye}~\Else~s)~(\Id{catch}_{Δ′}~\Id{hello}~())
%   \end{array}
% \end{align*}

%% This implies that the only way to ensure that $v$ has a computation type $A = () \to \Typing{C}{Δ′}$ whose effects match the context of the operation (e.g., $k : B \to \Typing{C}{Δ′}$), is to apply handlers of higher-order effect encodings (such as $\Op{op}$) before applying other handlers (such as $h$).
%% Otherwise, the effects contained in the value $v$ of $\Op{op}~v$ in \cref{eq:hdl-pretnar} above escape their scope, because handlers are not propagated into the computation contained in $v$.
%% Since we must apply handlers of higher-order effects first, this means that programs can contain at most one higher-order effect encoded in this way (otherwise, which handler do we apply first?).
%% Consequently, encoding computation parameters in terms of the value $v$ carried by an operation does not support modular definition, composition, and handling of higher-order effects.


%% For example, say we have the following program where the function $\Id{contains}~s_1~s_2$ is true iff string $s_2$ contains the string $s_1$:
%% %
%% \begin{equation*}
%%   \arraycolsep=1.4pt
%%   \begin{array}{ll}
%%     \arraycolsep=1.4pt
%%     \Id{loggy} &: \Typing{()}{\Effect{Output}}
%%     \\
%%     \Id{loggy} &= \Op{censor} \begin{array}[t]{l}
%%       (λ~s.~\If~(\Id{contains}~\String{foo}~s)~\Then~\String{}~\Else~s)
%%       \\
%%       (\Op{out}~\String{f}; \Op{out}~\String{o}; \Op{out}~\String{o})
%%     \end{array}
%%   \end{array}
%% \end{equation*}
%% %
%% Using the abbreviation above, the $\Id{loggy}$ program has a fixed interpretation: the program will never yield any output.
%% If we wanted to alter the interpretation of $\Op{censor}$ to apply the filter to each individual string $s$ of an $\Op{out}~s$ operation, we have no choice but to either redefine our program, or go back and modify the definition of $\Op{censor}$ and hope that that change is compatible with all other programs that use it.


\subsection{Solution: Elaboration Algebras}
\label{sec:solving-the-modularity-problem}

%We propose to modularize elaborations of higher-order effects into standard algebraic effects and handlers.
We propose to define operations such as $\Op{censor}$ from \cref{sec:modularity-problem} as \emph{modular elaborations} from a syntax of higher-order effects into algebraic effects and handlers.
To this end, we introduce a new type of \emph{computations with higher-order effects}, which can be modularly translated into computations with only standard algebraic effects:
%
\begin{equation*}
  \HTyping{A}{H} \ \xrightarrow{\Id{elaborate}}\ 
  \Typing{A}{Δ}  \ \xrightarrow{\Id{handle}}\
  \Id{Result}
\end{equation*}
%
Here $\HTyping{A}{H}$ is a computation type where $A$ is a return type and $H$ is a row comprising both algebraic and higher-order effects.
The key idea is that the higher-order effects in the row $H$ are modularly elaborated into a computation with effects given by the row $Δ$.
To achieve this, we define $\Id{elaborate}$ such that it can be modularly composed from separately defined elaboration cases, called elaboration \emph{algebras} (for reasons explained in \cref{sec:hefty-trees-and-algebras}). $\HTyping{A}{H} \Elabarr \Typing{A}{Δ}$ as the type of elaboration algebras that elaborate the higher-order effects in $H$ to $Δ$, we can modularly compose any pair of elaboration algebras $e_1 : \HTyping{A}{\Effect{H_1}} \Elabarr{} \Typing{A}{Δ}$ and $e_2 : \HTyping{A}{\Effect{H_2}} \Elabarr{} \Typing{A}{Δ}$ into an algebra $e_{12} : \HTyping{A}{\Effect{H_1,H_2}} \Elabarr{} \Typing{A}{Δ}$.\footnote{Readers familiar with data types \`{a} la carte~\citep{swierstra2008data} may recognize this as the usual closure of algebras under functor coproducts.}

Elaboration algebras are as simple to define as non-modular elaborations such as $\Id{censor}$ (\cref{sec:wa2}).
For example, here is the elaboration algebra for the higher-order $\Effect{Censor}$ effect whose only associated operation is the higher-order operation $\Op{censor_{op}} : (\Type{String} \to \Type{String}) \to \HTyping{A}{H} \to \HTyping{A}{H}$:
%
\begin{equation*}
  \arraycolsep=1.4pt
  \begin{array}{ll}
    \Id{eCensor} &: \HTyping{A}{\Effect{Censor}} \Elabarr{} \Typing{A}{\Effect{Output},Δ}
    \\
    \Id{eCensor} &(\Op{censor_{op}}~f~m;~k) = \Do~(x, s) \leftarrow (\With{\Id{hOut}}{m});~\Op{out}~(f~s);~k~x
  \end{array}
\end{equation*}
%
The implementation of $\Id{eCensor}$ is essentially the same as $\Id{censor}$, with two main differences.
First, elaboration happens in-context, so the value yielded by the elaboration is passed to the context (or continuation) $k$.
Second, and most importantly, programs that use the $\Op{censor_{op}}$ operation are now programmed against the interface given by $\Effect{Censor}$, meaning programs do not (and \emph{cannot}) make assumptions about how $\Op{censor_{op}}$ is elaborated.
As a consequence, we can modularly refine the elaboration of higher-order operations such as $\Op{censor_{op}}$, without modifying the programs that use the operations.
Similarly, we can define equational theories that constrain the behavior elaborations of higher-order operations, and write proofs about programs using higher-order operations that are valid for any elaboration that satisfies these equations.

For example, here is again a program which censors and replaces $\String{Hello}$ with $\String{Goodbye}$:\footnote{This program relies on the fact that it is generally possible to lift computation $\Typing{A}{Δ}$ to $\HTyping{A}{H}$ when $Δ \subseteq H$.}
\begin{equation*}
  \arraycolsep=1.4pt
  \begin{array}{ll}
    \Id{censorHello} &: \HTyping{()}{\Effect{Censor},\Effect{Output}}
    \\
    \Id{censorHello} &= \Op{censor_{op}}~(\lambda s.~ \If~(s \equiv \String{Hello})~\Then~\String{Goodbye}~\Else~s)~\Id{hello}
  \end{array}
\end{equation*}
Say we have a handler 
$\Id{hOut′} : (\Type{String} \to \Type{String}) \to
              \Typing{A}{\Effect{Output},Δ}
              \Rightarrow
              \Typing{(A \times \Type{String})}{Δ}$
which handles each operation $\Op{out}~s$ by pre-applying a censor function ($\Type{String} \to \Type{String}$) to $s$ before emitting it.
Using this handler, we can give an alternative elaboration of $\Op{censor_{op}}$ which post-processes output strings \emph{individually}:
%
\begin{equation*}
  \arraycolsep=1.4pt
  \begin{array}{ll}
    \Id{eCensor′} &: \HTyping{A}{\Effect{Censor}} \Elabarr{} \Typing{A}{\Effect{Output},Δ}
    \\
    \Id{eCensor′} &(\Op{censor_{op}}~f~m;~k) = \Do~(x,s) \leftarrow (\With{\Id{hOut′}~f}{m});~\Op{out}~s;~k~x
  \end{array}
\end{equation*}
%
In contrast, $\Effect{eCensor}$ applies the censoring function ($\Type{String} \to \Type{String}$) to the batch output of the computation argument of a $\Op{censor_{op}}$ operation.
The batch output of $\Id{hello}$ is \String{Hello world!} which is unequal to \String{Hello}, so $\Id{eCensor}$ leaves the string unchanged.
On the other hand, $\Id{eCensor′}$ censors the individually output \String{Hello}:%\footnote{In practice, there are no $\Effect{Output}$ operations left after elaborating $\Id{censorHello}$. However, this is not evident from the type of $\Id{censorHello}$. See \cref{sec:limitations} for a discussion of limitations.}
%
\begin{align*}
  \With{\Id{hOut}}{(\HWith{eCensor}{\Id{censorHello}})} &\equiv ((), \String{Hello world!})
  \\
  \With{\Id{hOut}}{(\HWith{eCensor′}{\Id{censorHello}})} &\equiv ((), \String{Goodbye world!})
\end{align*}
%
This gives higher-order operations the same modularity benefits as algebraic operations for defining programs.
In \cref{sec:modular-reasoning}, we show that these modularity benefits extend to program reasoning as well. 


\subsection{Contributions}
\label{sec:contributions}

This paper formalizes the ideas sketched in this introduction by shallowly embedding them in Agda.
However, the ideas transcend Agda.
Similar shallow embeddings can be implemented in other dependently typed languages, such as Idris~\citep{brady2013idris}; but also in less dependently typed languages like Haskell, OCaml, or Scala.\footnote{The artifact accompanying this paper~\citep{artifact} contains a shallow embedding of elaboration algebras in Haskell.}
By working in a dependently typed language we can state algebraic laws about interfaces of effectful operations, and prove that implementations of the interfaces respect the laws.
We make the following technical contributions:

\begin{itemize}
\item 
  \cref{sec:algebraic-effects} describes how to encode algebraic effects in Agda, revisits the modularity problem with higher-order operations, and summarizes how scoped effects and handlers address the modularity problem, for some (\emph{scoped} operations) but not all higher-order operations.
\item 
  \cref{sec:hefty-trees-and-algebras} presents our solution to the modularity problem with higher-order operations.
  Our solution is to (1) type programs as \emph{higher-order effect trees} (which we dub \emph{hefty trees}), and (2) build modular elaboration algebras for folding hefty trees into algebraic effect trees and handlers.
  The computations of type $\HTyping{A}{H}$ discussed in \cref{sec:solving-the-modularity-problem} correspond to hefty trees, and the elaborations of type $\HTyping{A}{H} \Elabarr \Typing{A}{Δ}$ correspond to hefty algebras.
\item
  \cref{sec:examples} presents examples of how to define hefty algebras for common higher-order effects from the literature on effect handlers.
\item 
  \cref{sec:modular-reasoning} shows that hefty algebras support formal and modular reasoning on a par with algebraic effects and handlers, by developing reasoning infrastructure that supports verification of equational laws for higher-order effects such as exception catching. Crucially, proofs of correctness of elaborations are compositional. When composing two proven correct elaboration, correctness of the combined elaboration follows immediately without requiring further proof work. 
\end{itemize}
%
\cref{sec:related} discusses related work and \cref{sec:conclusion} concludes.
The paper assumes a passing familiarity with dependent types.  We do not assume familiarity with Agda: we explain Agda-specific syntax and features when we use them.

An artifact containing the code of the paper and a Haskell embedding of the same ideas is available online~\citep{artifact}.
A subset of the contributions of this paper were previously published in a conference paper~\citep{DBLP:journals/pacmpl/PoulsenR23}.
While that version of the paper too discusses reasoning about higher-order effects, the correctness proofs were non-modular, in that they make assumptions about the order in which the algebraic effects implementing a higher-order effect are handled.
When combining elaborations, these assumptions are often incompatible, meaning that correctness proofs for the individual elaborations do not transfer to the combined elaboration.
As a result, one would have to re-prove correctness for every combination of elaborations. 
For this extended version, we developed reasoning infrastructure to support modular reasoning about higher-order effects in \cref{sec:modular-reasoning}, and proved that correctness of elaborations is preserved under composition of elaborations. 


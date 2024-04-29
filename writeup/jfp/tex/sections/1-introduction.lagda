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

Defining abstractions for programming with side effects is a research question with a long and rich history.
The goal is to define an interface of (possibly) side effecting operations where the interface encapsulates and hides irrelevant operational details about the operations and their side effects.
Such encapsulation makes it easy to refactor, optimize, or even change the behavior of a program, by changing the implementation of the interface.

Monads~\citep{DBLP:conf/lics/Moggi89} have long been the preferred solution to this research question.
However, \emph{algebraic effects and handlers}~\citep{Plotkin2009handlers} are emerging as an attractive alternative solution, due to the modularity benefits that they provide.
However, these modularity benefits do not apply to many common operations that take computations as arguments.

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
\newcommand{\Append}{+\kern-5pt+}
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

To understand the benefits of algebraic effects and handlers and the modularity problem with operations that take computations as parameters, we give a brief introduction to algebraic effects, based on the effect handlers tutorial by \citet{Pretnar15}.
Readers familiar with algebraic effects and handlers are encouraged to skim the code examples in this subsection and read its final paragraph.

Consider a simple operation $\Op{out}$ for output which takes a string as argument and returns the unit value.
Using algebraic effects and handlers its type is:
%
\begin{align*}
  \Op{out} &: \Type{String} \to \Typing{()}{\Effect{Output}}
\end{align*}
%
Here $\Effect{Output}$ is the \emph{effect} of the operation.
In general $\Typing{\Type{A}}{Δ}$ is a computation type where $\Type{A}$ is the return type and $Δ$ is a \emph{row} (i.e., unordered sequence) of \emph{effects}, where an \emph{effect} is a label associated with a set of operations.
A computation of type $\Typing{\Type{A}}{Δ}$ may \emph{only} use operations associated with an effect in $Δ$.
An effect can generally be associated with multiple operations (but not the other way around); however, the simple $\Effect{Output}$ effect that we consider is only associated with the operation $\Op{out}$.
Thus $\Typing{()}{\Effect{Output}}$ is the type of a computation which may call the $\Op{out}$ operation.

We can think of $\Effect{Output}$ as an interface that specifies the parameter and return type of $\Op{out}$.
The implementation of such an interface is given by an \emph{effect handler}.
An effect handler defines how to interpret operations in the execution context they occur in.
The type of an effect handler is $\Typing{A}{Δ}~\Rightarrow~\Typing{B}{Δ′}$, where $Δ$ is the row of effects before applying the handler and $Δ′$ is the row after.
For example, here is the type of an effect handler for $\Effect{Output}$:
%
\begin{equation*}
    \Id{hOut} : \Typing{A}{\Effect{Output},Δ}
                \Rightarrow
                \Typing{(A \times \Type{String})}{Δ}
\end{equation*}
%
%The type on the left of the double arrow is the computation before handling, and the type on the right is the computation after.
The $\Effect{Output}$ effect is being handled, so it is only present in the effect row on the left.\footnote{$\Effect{Output}$ could occur in $Δ$ too.  This raises the question: which $\Effect{Output}$ effect does a given handler actually handle?  We refer to the literature for answers to this question; see, e.g., the row treatment of \citet{morris2019abstracting}, the \emph{effect lifting} of \citet{DBLP:journals/pacmpl/BiernackiPPS18}, and the \emph{effect tunneling} of \citet{DBLP:journals/pacmpl/ZhangM19}.}
As the type suggests, this handler handles $\Op{out}$ operations by accumulating a string of output.
Below is the handler of this type:
%
\begin{equation*}
  \Id{hOut} =
    \Handler~\{
      \begin{array}[t]{ll}
        (\Return~x)~\mapsto~\Return~(x, \EmptyString)
          \\
        (\Op{out}~s;k)~\mapsto
          ~\Do~(y, s') ← k~();
          ~\Return~(y, s~\Append~s') ~\}
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
To this end, if $Δ = Δ₁,Δ₂$ and $h : \Typing{A}{Δ₁}~\Rightarrow~\Typing{B}{Δ₁′}$, then the expression $(\With{h}{m}) : \Typing{B}{Δ₁′,Δ₂}$ runs $m$ in the context of the handler $h$.
For example, consider:
\begin{align*}
  \Id{hello} &: \Typing{()}{\Effect{Output}}
  \\[-0.5ex]
  \Id{hello} &= \Op{out}~\String{Hello};~\Op{out}~\String{ world!}
\end{align*}
%
Using this, we can run $\Id{hello}$ in a scope with the handler $\Id{hOut}$ to compute the following result:
\begin{equation*}
  (\With{\Id{hOut}}{\Id{hello}}) \ \equiv\ ((), \String{Hello world!})
\end{equation*}

An attractive feature of algebraic effects and handlers is that programs such as $\Id{hello}$ are defined \emph{independently} of how the effectful operations they use are implemented.
This makes it is possible to refine, refactor, or even change the meaning of operations without having to modify the programs that use them.
For example, we can refine the meaning of $\Id{out}$ \emph{without modifying the $\Id{hello}$ program}, by using a different handler $\Id{hOut′}$ which prints output to the console.
%The types of algebraic effects and handlers enforces the type safety of such behavioral modifications.
However, some operations are challenging to express in a way that provides these modularity benefits.
%The next subsection explains the issue.


\subsection{The Modularity Problem with Higher-Order Operations}
\label{sec:modularity-problem}

Algebraic effects and handlers provide limited support for operations that accept computations as arguments (sometimes called \emph{higher-order operations}).
The limitation is subtle but follows from how handler cases are typed.
Following \citet{Plotkin2009handlers,Pretnar15}, the left and right hand sides of handler cases are typed as follows:
%
\begin{equation*}
  \Handler~\{~\cdots~(\Op{op}~\underbrace{v}_{A};\underbrace{k}_{B~\to~\Typing{C}{Δ′}})~\mapsto~\underbrace{c}_{\Typing{C}{Δ′}},~\cdots\}
\end{equation*}
%
Here it is only $k$ whose type is compatible with the right hand side.
In theory, the parameter type $v$ would also be compatible if $A = \Typing{C}{Δ′}$.
However, encoding computations as parameters in this way is non-modular.
The reason is that effect handlers are not applied recursively to parameters of operations~\citep{Plotkin2009handlers,Pretnar15}; i.e., if $h$ handles operations other than $\Op{op}$, then
%
\begin{equation*}
\With{h}{(\Do~x \leftarrow \Op{op}~v; m)}\
\equiv\
\Do~x \leftarrow \Op{op}~v; (\With{h}{m})
\end{equation*}
%
This implies that the only way to ensure that $v$ has type $A = \Typing{C}{Δ′}$ whose effects match the context of the operation (e.g., $k : B \to \Typing{C}{Δ′}$), is to apply handlers of higher-order effect encodings (such as $\Op{op}$) before applying other handlers (such as $h$).
In turn, this means that programs can contain at most one higher-order effect encoded in this way (otherwise, which handler do we apply first?).
Consequently, encoding computation parameters in terms of the value $v$ carried by an operation does not support modular definition, composition, and handling of higher-order effects.

A consequence of this restriction is that algebraic effects and handlers only support higher-order operations whose computation parameters are \emph{continuation-like}.
In particular, for any operation $\Op{op} : \Typing{A}{Δ} \to \cdots \to \Typing{A}{Δ} \to \Typing{A}{Δ}$ and any $m_1,\ldots,m_n$ and $k$,
%
\begin{equation*}
  \Do~x \leftarrow (\Op{op}~m_1\ldots m_n); k~x
  \ \equiv\ 
  \Op{op}~(\Do~x_1 \leftarrow m_1; k~x_1)\ldots(\Do~x_n \leftarrow m_n; k~x_n)
  \tag{\dag}
  \label{eqn:algebraicity}
\end{equation*}
%
This property, known as the \emph{algebraicity property}~\citep{PlotkinP03}, says that the computation parameter values $m_1,\ldots,m_n$ are only ever run in a way that \emph{directly} passes control to $k$.
Such operations can without loss of generality or modularity be encoded as operations \emph{without computation parameters}; e.g., $\Op{op}~m_1\ldots{}m_n = \Do~x \leftarrow \Op{op′}~(); \Id{select}~x$ where $\Op{op′} : () \to \Typing{D^n}{Δ}$ and $\Id{select} : D^n \to \Typing{A}{Δ}$ is a function that chooses between $n$ different computations using a data type $D^n$ whose constructors are $d_1,\ldots,d_n$ such that $\Id{select}~d_i = m_i$ for $i=1..n$.
Some higher-order operations obey the algebraicity property; many do not.
Examples of operations that do not include:
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
% \item Function abstraction as an effect: let $\Op{abs}~x~m$ be an operation that constructs a function value binding $x$ in computation $m$, $\Op{app}~v~m$ be an operation that applies a function value $v$ to an argument computation $m$, and $\Op{var}~x$ be an operation that dereferences a bound $x$.  Observe:
%   \[
%     \Do~(\Op{abs}~x~m₁); \Op{var}~x
%     \ \not\equiv\
%     \Op{abs}~x~(\Do~m₁; \Op{var}~x)
%   \]
\end{itemize}
%
% More examples of non-algebraic, higher-order operations can be found in, e.g., the popular Haskell \texttt{mtl} library.\footnote{\url{https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Writer-Lazy.html}}

It is, however, possible to elaborate higher-order operations into more primitive effects and handlers.
For example, $\Op{censor}$ can be elaborated into an inline handler application of $\Id{hOut}$:
%
\begin{gather*}
  \arraycolsep=1.4pt
  \begin{array}{ll}
    \Op{censor} &: (\Type{String} \to \Type{String}) \to \Typing{A}{\Effect{Output},Δ} \to \Typing{A}{\Effect{Output},Δ}
    \\
    \Op{censor} &f~m = \Do~(x, s) \leftarrow (\With{\Id{hOut}}{m});~\Op{out}~(f~s);~\Return~x
  \end{array}
\end{gather*}
%
The other higher-order operations above can be defined in a similar manner.

Elaborating higher-order operations into standard algebraic effects and handlers as illustrated above is a key use case that effect handlers were designed for~\citep{Plotkin2009handlers}.
However, elaborating operations in this way means the operations are not a part of any effect interface.
So, unlike plain algebraic operations, the only way to refactor, optimize, or change the semantics of higher-order operations defined in this way is to modify or copy code.
In other words, we forfeit one of the key attractive modularity features of algebraic effects and handlers.

This modularity problem with higher-order effects (i.e., effects with higher-order operations) was first observed by \citet{WuSH14} who proposed \emph{scoped effects and handlers}~\citep{WuSH14,PirogSWJ18,YangPWBS22} as a solution.
Scoped effects and handlers have similar modularity benefits as algebraic effects and handlers, but works for a wider class of effects, including many higher-order effects.
However, \citet{BergSPW21} recently observed that operations that defer computation, such as evaluation strategies for $\lambda$ application or \emph{(multi-)staging} \citep{TahaS00}, are beyond the expressiveness of scoped effects.
Therefore, \citet{BergSPW21} introduced another flavor of effects and handlers that they call \emph{latent effects and handlers}.

In this paper we present a (surprisingly) simple alternative solution to the modularity problem with higher-order effects, which only uses standard effects and handlers and off-the-shelf generic programming techniques known from, e.g., \emph{data types \`{a} la carte}~\citep{swierstra2008data}.

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


\subsection{Solving the Modularity Problem: Elaboration Algebras}
\label{sec:solving-the-modularity-problem}

%We propose to modularize elaborations of higher-order effects into standard algebraic effects and handlers.
We propose to define elaborations such as $\Op{censor}$ from \cref{sec:modularity-problem} in a modular way.
To this end, we introduce a new type of \emph{computations with higher-order effects} which can be modularly elaborated into computations with only standard algebraic effects:
%
\begin{equation*}
  \HTyping{A}{H} \ \xrightarrow{\Id{elaborate}}\ 
  \Typing{A}{Δ}  \ \xrightarrow{\Id{handle}}\
  \Id{Result}
\end{equation*}
%
Here $\HTyping{A}{H}$ is a computation type where $A$ is a return type and $H$ is a row comprising both algebraic and higher-order effects.
The idea is that the higher-order effects in the row $H$ are modularly elaborated into the row $Δ$.
To achieve this, we define $\Id{elaborate}$ such that it can be modularly composed from separately defined elaboration cases, which we call elaboration \emph{algebras} (for reasons we explain in \cref{sec:hefty-trees-and-algebras}).
Using $\HTyping{A}{H} \Elabarr \Typing{A}{Δ}$ as the type of elaboration algebras that elaborate the higher-order effects in $H$ to $Δ$, we can modularly compose any pair of elaboration algebras $e_1 : \HTyping{A}{\Effect{H_1}} \Elabarr{} \Typing{A}{Δ}$ and $e_2 : \HTyping{A}{\Effect{H_2}} \Elabarr{} \Typing{A}{Δ}$ into an algebra $e_{12} : \HTyping{A}{\Effect{H_1,H_2}} \Elabarr{} \Typing{A}{Δ}$.\footnote{Readers familiar with data types \`{a} la carte~\citep{swierstra2008data} may recognize this as algebra composition.}

Elaboration algebras are as simple to define as non-modular elaborations such as $\Id{censor}$ (\cref{sec:modularity-problem}).
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
The implementation of $\Id{eCensor}$ is essentially the same as $\Id{censor}$.
There are two main differences.
First, elaboration happens in-context, so the value yielded by the elaboration is passed to the context (or continuation) $k$.
Second, and most importantly, programs that use the $\Op{censor_{op}}$ operation are now programmed against the interface given by $\Effect{Censor}$, meaning programs do not (and \emph{cannot}) make assumptions about how $\Op{censor_{op}}$ is elaborated.
As a consequence, we can modularly refine the elaboration of higher-order operations such as $\Op{censor_{op}}$, without modifying the programs that use the operations.
For example, the following program censors and replaces $\String{Hello}$ with $\String{Goodbye}$:\footnote{This program relies on the fact that it is generally possible to lift computation $\Typing{A}{Δ}$ to $\HTyping{A}{H}$ when $Δ \subseteq H$.}
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
    \Id{eCensor′} &(\Op{censor_{op}}~f~m;~k) = \Do~x \leftarrow (\With{\Id{hOut′}~f}{m});~\Op{out}~s;~k~x
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
Higher-order operations now have the same modularity benefits as algebraic operations.


\subsection{Contributions}
\label{sec:contributions}

This paper formalizes the ideas sketched in this introduction by shallowly embedding them in Agda.
However, the ideas transcend Agda.
Similar shallow embeddings can be implemented in other dependently typed languages, such as Idris~\citep{brady2013idris}; but also in less dependently typed languages like Haskell, OCaml, or Scala.\footnote{The artifact accompanying this paper~\citep{heftyalgebraspopl23artifact} contains a shallow embedding of elaboration algebras in Haskell.}
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
  \cref{sec:laws} shows that hefty algebras support formal reasoning on a par with algebraic effects and handlers, by verifying algebraic laws of higher-order effects for exception catching.
\item
  \cref{sec:examples} presents examples of how to define hefty algebras for common higher-order effects from the literature on effect handlers.
\end{itemize}
%
\cref{sec:related} discusses related work and \cref{sec:conclusion} concludes.
An artifact containing the code of the paper and a Haskell embedding of the same ideas is available online~\citep{heftyalgebraspopl23artifact}.


\endinput

Algebraic effects and handlers~\citep{Plotkin2009handlers} are a relatively new, and increasingly popular, solution to the problem of defining abstractions for programming constructs with side effects.
Part of the reason behind its increasing popularity is that the solution supports a high degree of modularity, and requires less glue code than previous solutions like .
This modularity, in theory, makes it possible to use algebraic effects and handlers to create reusable libraries of effectful abstractions, similar to the popular libraries for monad transformers in general use in the Haskell and Scala communities.
In practice, most recent libraries (e.g., \cite{FIXME}) rely on a different, more general, notion of effect handler known as \emph{scoped effects and handlers}~\cite{WuSH14,PirogSWJ18,YangPWBS22}.
The reason is that algebraic effects and handlers have a modularity problem with so-called \emph{higher-order operations} (i.e., operations that have computations as parameters).

To understand the problem, we first informally summarize what notion of modularity we are concerned with.
We wish to support a programming paradigm where programmers can (1) declare an interface of (possibly) side effectful operations that we program against; and (2) run programs by importing separately defined interface implementations.
The latter requirement often requires some glue code.
Algebraic effects and handlers generally requires less glue code than, e.g., monad transformers.

Interface implementations should be separately definable, and 

- ability to declare an interface separately from its definition

- ability to seamlessly depend on different interfaces

- ability to implement each interface separately with minimal glue code



 programmers to declare and work with effectful operations whose semantics can be defined modularly and separately from the programs use them.
In other words

% Benefit over monad transformers: programs with different effects can be seamlessly composed and handled without having to ``lift'' operations across monad transformer stacks

Modularity: we can change the semantics of an effect without having to recompile the program that uses the effect

problem: higher-order effects don't enjoy these properties

main solutions in previous work:

- scoped effects -- implemented in various Haskell frameworks
- latent effects -- adds support for a class of constructs that are not commonly defined in terms of scoped effects
- Frank, Koka, provides support for writing polymorphic handlers
  + less flexible than scoped effects and latent effects -- e.g., global state semantics
  + requires changing handler to get transactional state semantics

in this paper:

a simple alternative: desugarings like the ones you can express in Koka and Frank, but modular by construction

treat computation as syntax to get same benefits as with plain algebraic effects:

separation of concerns

modularity

we use Agda throughout and mechanically verify algebraic laws for both higher-order and algebraic operations

Contributions:


\cite{}

\clearpage

%%% Local Variables:
%%% reftex-default-bibliography: ("../references.bib")
%%% End:

\begin{code}[hide]

{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module tex.sections.2-algebraic-effects where

open import Level

open import Function
open import Function.Construct.Identity
open import Function.Construct.Symmetry
open import Function.Construct.Composition

open import Data.Empty
open import Data.Unit
open import Data.Bool hiding (_≤_)
open import Data.Maybe using (Maybe; nothing; just; maybe)
open import Data.Sum
open import Data.Nat hiding ( _≤_)
open import Data.String
open import Data.Product using (_×_; _,_ ; Σ ; ∃ ; proj₁ ; proj₂)
-- open import Data.List
-- open import Data.List.Membership.Propositional
-- open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Effect.Monad
open ≡-Reasoning
open import tex.sections.Postulates.Extensionality
open import Relation.Unary

private variable a b c : Level
                 A A′ B B′ C P : Set a
                 F G : Set a → Set b
\end{code}

\section{Algebraic Effects and Handlers in Agda}
\label{sec:algebraic-effects}

This section describes how to encode algebraic effects and handlers in Agda.  We
do not assume familiarity with Agda and explain Agda specific notation in
footnotes.
\cref{sec:free-monad,sec:row-insertion,sec:fold-bind-free,sec:effect-handlers}
defines algebraic effects and handlers; \cref{sec:higher-order-effects} revisits
the problem of defining higher-order effects using algebraic effects and
handlers; and \cref{sec:scoped-effects} discusses how scoped
effects~\citep{WuSH14,PirogSWJ18,YangPWBS22} solves the problem for \emph{scoped} operations but not all higher-order operations.


\subsection{Algebraic Effects and The Free Monad}
\label{sec:free-monad}

\begin{code}[hide]
module FreeModule where
\end{code}

We encode algebraic effects in Agda by representing computations as an abstract
syntax tree given by the \emph{free monad} over an \emph{effect signature}.
Such effect signatures are
traditionally~\citep{awodey2010categorytheory,swierstra2008data,KiselyovI15,WuSH14,KammarLO13}
given by a \emph{functor}; i.e., a type of kind \ad{Set}~\as{→}~\ad{Set}
together with a (lawful) mapping function.\footnote{\ad{Set} is the type of
  types in Agda. More generally, functors mediate between different
  \emph{categories}. For simplicity, this paper only considers \emph{endofunctors} on
  \ad{Set}, where an endofunctor is a functor whose domain and codomain coincides; e.g., \ad{Set}~\as{→}~\ad{Set}.}  In our Agda implementation, effect signature functors are defined
by giving a \emph{container}~\citep{AbbottAG03,Abbott2005containers}.  Each
container corresponds to a value of type $\ad{Set}~→~\ad{Set}$ that is both
\emph{strictly
  positive}\footnote{\url{https://agda.readthedocs.io/en/v2.6.2.2/language/positivity-checking.html}}
and \emph{universe consistent}\footnote{\url{https://agda.readthedocs.io/en/v2.6.2.2/language/universe-levels.html}}~\citep{martin-lof1984intuitionistic},
meaning they are a constructive approximation of endofunctors on \ad{Set}.
Effect signatures are given by a (dependent) record
type:\footnote{\url{https://agda.readthedocs.io/en/v2.6.2.2/language/record-types.html}}
\footnote{The type of effect rows has type \ad{Set₁} instead of \ad{Set}.  To
  prevent logical inconsistencies, Agda has a hierarchy of types where
  \ad{Set}~\as{:}~\ad{Set₁}, \ad{Set₁}~\as{:}~\ad{Set₂}, etc.}
%
\begin{code}
  record Effect : Set₁ where
    field  Op   : Set
           Ret  : Op → Set
\end{code}
%
\begin{code}[hide]
  open Effect
  variable Δ Δ′ Δ″ Δ₀ Δ₁ Δ₂ Δ₃ : Effect
           X Y : Set 
\end{code}
%
Here, \aF{Op} is the set of operations, and \aF{Ret} defines the \emph{return
  type} for each operation in the set \aF{Op}.  The extension of an effect
signature, $⟦\_⟧$, reflects its input of type $\ad{Effect}$ as a value of type
$\ad{Set}~→~\ad{Set}$:\footnote{Here, \ad{Σ}~\as{:}~\as{(}\ab{A}~\as{:}~\ad{Set}~\as{)}~\as{→}~\as{(}\ab{A}~\as{→}~\ad{Set}\as{)}~\as{→}~\ad{Set} is a \emph{dependen sum}.}
%
\begin{code}
  ⟦_⟧ : Effect → Set → Set
  ⟦ Δ ⟧ X = Σ (Op Δ) λ op → Ret Δ op → X 
\end{code}
%
The extension of an effect $Δ$ into $\ad{Set}~→~\ad{Set}$ is indeed a functor,
as witnessed by the following function:\footnote{To show that this is truly a functor, we should also prove that \af{map-sig} satisfies the \emph{functor laws}.  We will not make use of these functor laws in this paper, so we omit them.}
%
\begin{code}
  map-sig : (X → Y) → ⟦ Δ ⟧ X → ⟦ Δ ⟧ Y
  map-sig f (op , k) = ( op , f ∘ k ) 
\end{code}

As discussed in the introduction, computations may use multiple different
effects. Effect signatures are closed under co-products:\footnote{The \ad{\_⊕\_} function uses \emph{copattern
    matching}:
  \url{https://agda.readthedocs.io/en/v2.6.2.2/language/copatterns.html}. The
  \aF{Op} line defines how to compute the \aF{Op} field of the record produced
  by the function; and similarly for the \aF{Ret} line.}  \footnote{\ad{\_⊎\_}
  is a \emph{disjoint sum} type from the Agda standard library.  It has two
  constructors, \ac{inj₁}~\as{:}~\ab{A}~\as{→}~\ab{A}~\ad{⊎}~\ab{B} and
  \ac{inj₂}~\as{:}~\ab{B}~\as{→}~\ab{A}~\ad{⊎}~\ab{B}.  The \ad{[\_,\_]}
  function (also from the Agda standard library) is the \emph{eliminator} for
  the disjoint sum type.  Its type is
  \ad{[\_,\_]}~\as{:}~\as{(}\ab{A}~\as{→}~\ab{X}\as{)~→~(}\ab{B}~\as{→}~\ab{X}\as{)}~\as{→}~\as{(}\ab{A}~\ad{⊎}~\ab{B}\as{)}~\as{→}~\ab{X}.}
%
\begin{code}[hide]
  infixr 12 _⊕_
\end{code}
\begin{code}
  _⊕_ : Effect → Effect → Effect
  Op   (Δ₁ ⊕ Δ₂) = Op Δ₁ ⊎ Op Δ₂
  Ret  (Δ₁ ⊕ Δ₂) = [ Ret Δ₁ , Ret Δ₂ ]
\end{code}
%
We compute the co-product of two effect signatures by taking the disjoint sum of
their operations and combining the return type mappings pointwise.
We use co-products to encode effect rows. For example, The effect
\ab{Δ₁}~\ad{⊕}~\ab{Δ₂} corresponds to the row union denoted as $Δ₁,Δ₂$ in the
introduction.

The syntax of computations with effects \ab{Δ} is given by the free monad over
\ab{Δ}.  We encode the free monad as follows:
%
\begin{code}
  data Free (Δ : Effect) (A : Set) : Set where
    pure    : A                 → Free Δ A
    impure  : ⟦ Δ ⟧ (Free Δ A)  → Free Δ A
\end{code}

Here, \ac{pure} is a computation with no side-effects, whereas \ac{impure} is an
operation whose syntax is given by the functor \af{⟦}~\ab{Δ}~\af{⟧}.  By
applying this functor to \ad{Free}~\ab{Δ}~\as{A}, we encode an operation whose
\emph{continuation} may contain more effectful operations.\footnote{By unfolding
the definition of \ad{⟦\_⟧} one can see that our definition of the free monad is
identical to the I/O trees of \citet{DBLP:conf/csl/HancockS00}, or the so-called
\emph{freer monad} of \citet{KiselyovI15}.}  To see in what sense, let us
consider an example.


\paragraph*{Example.}
  The data type on the left below defines an operation for outputting a string.
  On the right is its corresponding effect signature.\\
  \begin{minipage}{0.495\linewidth}
  \begin{code}
  data OutOp : Set where
    out : String → OutOp
  \end{code}
  \end{minipage}
  \hfill\vline\hfill
  \begin{minipage}{0.495\linewidth}
  \begin{code}
  Output : Effect
  Op   Output          = OutOp
  Ret  Output (out s)  = ⊤
  \end{code}
\end{minipage}\\



The effect signature on the right says that \ac{out} returns a unit value
(\ad{⊤} is the unit type).  Using this, we can write a simple hello world
corresponding to the $\Id{hello}$ program from \cref{sec:1-introduction}:
  \begin{code}
  hello : Free Output ⊤
  hello = impure (out "Hello" , λ _ → impure (out " world!" , λ x → pure x))
  \end{code}
  \cref{sec:free-monad} shows how to make this program more readable by using
  monadic \ak{do} notation.

  The \af{hello} program above makes use of just a single effect.  Say we want
  to use another effect, \ad{Throw}, with a single operation, \ac{throw}, which
  represents throwing an exception (therefore having the empty
  type \af{⊥} as its return type):\\
\begin{minipage}{0.495\linewidth}
\begin{code}
  data ThrowOp : Set where
    throw : ThrowOp
\end{code}
\end{minipage}
\hfill\vline\hfill
\begin{minipage}{0.495\linewidth}
\begin{code}
  Throw : Effect
  Op   Throw = ThrowOp
  Ret  Throw throw = ⊥
\end{code}
\end{minipage}\\
%
Programs that use multiple effects, such as \ad{Output} and \ad{Throw}, are
unnecessarily verbose.  For example, consider the following program which prints
two strings before throwing an exception:\footnote{\ad{⊥-elim} is the eliminator
  for the empty type, encoding the \emph{principle of explosion}:
  \ad{⊥-elim}~\as{:}~\ad{⊥}~\as{→}~\ab{A}.}
%
\begin{code}
  hello-throw : Free (Output ⊕ Throw) A
  hello-throw =  impure (inj₁ (out "Hello") , λ _ →
                   impure (inj₁ (out " world!") , λ _ →
                     impure (inj₂ throw , ⊥-elim)))
\end{code}
%
To reduce syntactic overhead, we use \emph{row insertions} and \emph{smart
  constructors}~\citep{swierstra2008data}.


\subsection{Row Insertions and Smart Constructors}
\label{sec:row-insertion}

A \emph{smart constructor} constructs an effectful computation comprising a single operation.
The type of this computation is polymorphic in what other effects the computation has.
For example, the type of a smart constructor for the \ac{out} effect is:
%
\begin{code}[hide]
  postulate
    _≲⅋_ : (Δ₁ Δ₂ : Effect) → Set₁
\end{code}
\begin{code}
    ‵out⅋ : ⦃ Output ≲⅋ Δ ⦄ → String → Free Δ ⊤
\end{code}
%
Here, the \as{⦃}~\ad{Output}~\ad{≲}~\ab{Δ}~\as{⦄} type declares the row insertion witness as an \emph{instance argument} of \af{‵out}.
Instance arguments in Agda are conceptually similar to type class constraints in
Haskell: when we call \af{‵out}, Agda will attempt to automatically find a
witness of the right type, and implicitly pass this as an argument.\footnote{For
  more details on how instance argument resolution works, see the Agda
  documentation:
  \url{https://agda.readthedocs.io/en/v2.6.2.2/language/instance-arguments.html}}
Thus, calling \af{‵out} will automatically inject the \ad{Output} effect into
some larger effect row \ab{Δ}.

We define the \ad{≲} order on effect rows in terms of a different
\ab{Δ₁}~\ad{∙}~\ab{Δ₂}~\ad{≈}~\ab{Δ} which witnesses that any operation of
\ab{Δ} is isomorphic to \emph{either} an operation of \ab{Δ₁} \emph{or} an
operation of \ab{Δ₂}:\footnote{Here \as{∀~\{}\ab{X}\as{\}} is implicit universal quantification over an $X~\as{:}~\ad{Set}$: \url{https://agda.readthedocs.io/en/v2.6.2.2/language/implicit-arguments.html}}\footnote{\ad{↔} is the type of an \emph{isomorphism} on \ad{Set} from the Agda Standard Library.  It is given by a record with two fields: the \aF{to} field represents the $\rightarrow$ direction of the isomorphism, and \aF{from} field represents the $\leftarrow$ direction of the isomorphism.}
%
\begin{code}
  record _∙_≈_ (Δ₁ Δ₂ Δ : Effect) : Set₁ where
    field reorder : ∀ {X} → ⟦ Δ₁ ⊕ Δ₂ ⟧ X ↔ ⟦ Δ ⟧ X
\end{code}
\begin{code}[hide]
  open _∙_≈_ 
\end{code}
%
Using this, the \ad{≲} order is defined as follows:
%
\begin{code}
  _≲_ : (Δ₁ Δ₂ : Effect) → Set₁
  Δ₁ ≲ Δ₂ = Σ Effect (λ Δ′ → Δ₁ ∙ Δ′ ≈ Δ₂)
\end{code}
%
It is straightforward to show that \ad{≲} is a \emph{preorder}; i.e., that it is a \emph{reflexive} and \emph{transitive} relation.
%
\begin{code}[hide]
  postulate ≲-trans : Δ₁ ≲ Δ₂ → Δ₂ ≲ Δ → Δ₁ ≲ Δ
  module _ where
    open Inverse
\end{code}


We can also define the following function, which uses a \ab{Δ₁}~\ad{≲}~\ab{Δ₂} witness to coerce an operation of effect type \ab{Δ₁} into an operation of some larger effect type \ab{Δ₂}.\footnote{The dot notation \ab{w}~\as{.}\aF{reorder} projects the \aF{reorder} field of the record \ab{w}.}
%
\begin{code}
    inj : ⦃ Δ₁ ≲ Δ₂ ⦄ → ⟦ Δ₁ ⟧ A → ⟦ Δ₂ ⟧ A
    inj ⦃ _ , w ⦄ (c , k) = w .reorder .to (inj₁ c , k)
\end{code}
\begin{code}[hide]
    injₗ : ⦃ Δ₁ ∙ Δ₂ ≈ Δ ⦄ → ⟦ Δ₁ ⟧ A → ⟦ Δ ⟧ A
    injₗ ⦃ w ⦄ (c , k) = w .reorder .to (inj₁ c , k)
\end{code}
%

Furthermore, we can freely coerce the operations of a computation from one
effect row type to a different effect row type:\footnote{The notation \af{∀[\_]} is from the Agda Standard library, and is defined as follows: \af{∀[}~\ab{P}~\af{]}~\as{=~∀}~\ab{x}~\as{→}~\ab{P~x}.}
\footnote{We can think
of the \af{hmap-free} function as a ``higher-order'' map for \ad{Free}: given a natural
transformation between (the extension of) signatures, we can can transform the
signature of a computation.  This amounts to the observation that \ad{Free} is a
functor over the category of containers and container morphisms; assuming
\af{hmap-free} preserves naturality.}
%
\begin{code}
  hmap-free : ∀[ ⟦ Δ₁ ⟧ ⇒ ⟦ Δ₂ ⟧ ] → ∀[ Free Δ₁ ⇒ Free Δ₂ ] 
  hmap-free θ (pure x)          = pure x
  hmap-free θ (impure (c , k))  = impure (θ (c , hmap-free θ ∘ k))
\end{code}
%
Using this infrastructure, we can now implement a generic \ad{inject} function which
lets us define smart constructors for operations such as the \ac{out} operation
discussed in the previous subsection.
%
\begin{code}
  inject : ⦃ Δ₁ ≲ Δ₂ ⦄ → Free Δ₁ A → Free Δ₂ A
  inject = hmap-free inj

  ‵out : ⦃ Output ≲ Δ ⦄ → String → Free Δ ⊤
  ‵out s = inject (impure (out s , pure)) 
\end{code}
%


\subsection{Fold and Monadic Bind for \ad{Free}}
\label{sec:fold-bind-free}

Since $\ad{Free}~\ab{Δ}$ is a monad, we can sequence computations using
\emph{monadic bind}, which is naturally defined in terms of the fold over
\ad{Free}.
%
\begin{code}[hide]
  Alg : (Δ : Effect) (A : Set) → Set
  Alg Δ A = ⟦ Δ ⟧ A → A
\end{code}
\begin{code}
  fold  :  (A → B) → Alg Δ B → Free Δ A → B
  fold g a (pure x)       = g x
  fold g a (impure (op , k))  = a (op , fold g a ∘ k)
\end{code}
\begin{code}
  Alg⅋ : (Δ : Effect) (A : Set) → Set
  Alg⅋ Δ A = ⟦ Δ ⟧ A → A
\end{code}
%
Besides the input computation to be folded (last parameter), the fold is
parameterized by a function \ab{A}~\as{→}~\ab{B} (first parameter) which folds a
\ac{pure} computation, and an \emph{algebra} \af{Alg}~\ab{Δ}~\ab{A} (second
parameter) which folds an \ac{impure} computation.  We call the latter an
algebra because it corresponds to an
$F$-algebra~\citep{arbib1975arrows,DBLP:books/daglib/0069193} over the signature
functor of $\ad{Δ}$, denoted $F_{Δ}$. That is, a tuple $(A, α)$ where $A$ is an
object called the \emph{carrier} of the algebra, and \ab{α} a morphism
$F_{Δ}(A) \to A$.  Using \af{fold}, monadic bind for the free monad is defined
as follows:
\begin{code}
  _𝓑_ : Free Δ A → (A → Free Δ B) → Free Δ B
  m 𝓑 g = fold g impure m
\end{code}
%
\begin{code}[hide]
  private _>>=_ = _𝓑_

  fold≡ : (m : Free Δ A) → fold pure impure m ≡ m
  fold≡ (pure x) = refl
  fold≡ (impure (op , k)) = cong (impure ∘ (op ,_)) (extensionality (λ x → fold≡ (k x)))

  fmap : (A → B) → Free Δ A → Free Δ B
  fmap f = fold (pure ∘ f) impure

  Free-unitₗ-≡ : {x : A} (k : A → Free Δ B)
               → pure x 𝓑 k ≡ k x
  Free-unitₗ-≡ _ = refl

  Free-unitᵣ-≡ : (m : Free Δ A)
               → m 𝓑 pure ≡ m
  Free-unitᵣ-≡ (pure x) = refl
  Free-unitᵣ-≡ (impure (op , k)) = cong (λ x → impure (op , x)) (extensionality $ λ y → Free-unitᵣ-≡ $ k y) 

  Free-assoc-≡ : (m : Free Δ A) (k₁ : A → Free Δ B) (k₂ : B → Free Δ C)
               → (m 𝓑 k₁) 𝓑 k₂ ≡ m 𝓑 (λ x → (k₁ x) 𝓑 k₂)
  Free-assoc-≡ (pure x) k₁ k₂ = refl
  Free-assoc-≡ (impure (op , k)) k₁ k₂ = cong (λ x → impure (op , x)) (extensionality $ λ x → Free-assoc-≡ (k x) k₁ k₂)

  Free-cong₂ : (m : Free Δ A) (k k' : A → Free Δ B)
             → (∀ x → k x ≡ k' x)
             → (m 𝓑 k) ≡ (m 𝓑 k')
  Free-cong₂ (pure x) k k' eq = eq _
  Free-cong₂ (impure (op , k₁)) k k' eq = cong (λ x → impure (op , x)) $ extensionality $ λ x →
    cong (λ y → (k₁ x) 𝓑 y) $ extensionality eq
\end{code}
%
Intuitively, \ab{m}~\af{𝓑}~\ab{g} concatenates \ab{g} to all the leaves in the computation \ab{m}.
%
\paragraph*{Example.}
The following defines a smart constructor for \ac{throw}:
\begin{code}
  ‵throw : ⦃ Throw ≲ Δ ⦄ → Free Δ A
\end{code}
\begin{code}[hide]
  ‵throw = inject (impure (throw , ⊥-elim))

  _>>_ : Free Δ A → Free Δ B → Free Δ B
  m₁ >> m₂ = m₁ 𝓑 λ _ → m₂
\end{code}
Using this and the definition of \ad{𝓑} above, we can use \textbf{do}-notation in Agda to make the \af{hello-throw} program from \cref{sec:free-monad} more readable:
\begin{code}
  hello-throw₁ : ⦃ Output ≲ Δ ⦄ → ⦃ Throw ≲ Δ ⦄ → Free Δ A
  hello-throw₁ = do ‵out "Hello"; ‵out " world!"; ‵throw
\end{code}

\noindent
This illustrates how we use the free monad to write effectful programs against
an interface given by an effect signature.  Next, we define \emph{effect
  handlers}.


\subsection{Effect Handlers}
\label{sec:effect-handlers}

An effect handler implements the interface given by an effect signature,
interpreting the syntactic operations associated with an effect.  Like monadic
bind, effect handlers can be defined as a fold over the free monad.  The
following type of \emph{parameterized handlers}~\cite[\S 2.2]{Leijen17} defines how to fold respectively
\ac{pure} and \ac{impure} computations:\footnote{A simpler type of handler could omit the parameter; i.e., \af{⟨}~\ab{A}~\af{!}~\ab{Δ}~\af{⇒}~\ab{B}~\af{!}~\ab{Δ′}~\af{⟩}, for some \ab{A},\ab{B}~\as{:}~\ad{Set} and \ab{Δ},\ab{Δ′}~\as{:}~\ad{Effect}.  As demonstrated in, e.g., the work of \citet[\S 2.4]{Pretnar15}, this type of handler can leverage host language binding to handle, e.g., the \emph{state effect} which we discuss later.  The style of parameterized handler we use here follows the exposition of, e.g., \citet{WuSH14,WuS15}.}
%
\begin{code}
  record ⟨_!_⇒_⇒_!_⟩ (A : Set) (Δ : Effect) (P : Set) (B : Set) (Δ′ : Effect) : Set₁ where
    field  ret  : A → P → Free Δ′ B
           hdl  : Alg Δ (P → Free Δ′ B)
\end{code}
%
\begin{code}[hide]
  open ⟨_!_⇒_⇒_!_⟩

  open Inverse

  _↦_ : Effect → Effect → Set₁
  Δ₁ ↦ Δ₂ = ∀[ ⟦ Δ₁ ⟧ ⇒ ⟦ Δ₂ ⟧ ]

  injˡ : ∀ Δ₂ → Δ₁ ↦ (Δ₁ ⊕ Δ₂)
  injˡ _ (c , k) = (inj₁ c , k)

  injʳ : ∀ Δ₁ → Δ₂ ↦ (Δ₁ ⊕ Δ₂)
  injʳ _ (c , k) = (inj₂ c , k)

  swapᶜ : ∀ Δ₁ Δ₂ → (Δ₁ ⊕ Δ₂) ↦ (Δ₂ ⊕ Δ₁)
  swapᶜ _ _ (inj₁ c , k) = (inj₂ c , k)
  swapᶜ _ _ (inj₂ c , k) = (inj₁ c , k)


  swapᶜ-involutive : ∀ {A} (x : ⟦ Δ₁ ⊕ Δ₂ ⟧ A) → swapᶜ Δ₂ Δ₁ (swapᶜ Δ₁ Δ₂ x) ≡ x
  swapᶜ-involutive (inj₁ x , k) = refl
  swapᶜ-involutive (inj₂ y , k) = refl

  ⊕-comm : ∀ Δ₁ Δ₂ → (∀ {X} → ⟦ Δ₁ ⊕ Δ₂ ⟧ X ↔ ⟦ Δ₂ ⊕ Δ₁ ⟧ X)
  ⊕-comm Δ₁ Δ₂ = record
    { to        = swapᶜ Δ₁ Δ₂
    ; from      = swapᶜ Δ₂ Δ₁
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   = (λ where refl → swapᶜ-involutive _) ,  (λ where refl → swapᶜ-involutive _)
    }

  ⊕-congˡ : ∀ Δ₁ Δ₂ Δ → (∀ {X} → ⟦ Δ₁ ⟧ X ↔ ⟦ Δ₂ ⟧ X) → (∀ {X} → ⟦ Δ₁ ⊕ Δ ⟧ X ↔ ⟦ Δ₂ ⊕ Δ ⟧ X)
  ⊕-congˡ Δ₁ Δ₂ Δ iso = record
    { to        = to′
    ; from      = from′
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   = (λ where refl → cong-inverseˡ _) , λ where refl → cong-inverseʳ _ 
    }
    where
      to′ : ∀[ ⟦ Δ₁ ⊕ Δ ⟧ ⇒ ⟦ Δ₂ ⊕ Δ ⟧ ]
      to′ (inj₁ c , k) = injˡ Δ (iso .to (c , k))
      to′ (inj₂ c , k) = (inj₂ c , k)

      from′ : ∀[ ⟦ Δ₂ ⊕ Δ ⟧ ⇒ ⟦ Δ₁ ⊕ Δ ⟧ ]
      from′ (inj₁ c , k) = injˡ Δ (iso .from (c , k))
      from′ (inj₂ c , k) = (inj₂ c , k)

      cong-inverseˡ : ∀ x → to′ (from′ x) ≡ x
      cong-inverseˡ (inj₁ c , k) = cong (injˡ Δ) (Inverse.inverse iso .proj₁ refl)
      cong-inverseˡ (inj₂ c , k) = refl

      cong-inverseʳ : ∀ x → from′ (to′ x) ≡ x 
      cong-inverseʳ (inj₁ c , k) = cong (injˡ Δ) (Inverse.inverse iso .proj₂ refl)
      cong-inverseʳ (inj₂ c , k) = refl


  assocᶜʳ : ∀ Δ₁ Δ₂ Δ₃ → ((Δ₁ ⊕ Δ₂) ⊕ Δ₃) ↦ (Δ₁ ⊕ (Δ₂ ⊕ Δ₃))
  assocᶜʳ _ _ _ (inj₁ (inj₁ c) , k) = (inj₁ c , k)
  assocᶜʳ _ _ _ (inj₁ (inj₂ c) , k) = (inj₂ (inj₁ c) , k)
  assocᶜʳ _ _ _ (inj₂ c        , k) = (inj₂ (inj₂ c) , k)

  assocᶜˡ : ∀ Δ₁ Δ₂ Δ₃ → (Δ₁ ⊕ (Δ₂ ⊕ Δ₃)) ↦ ((Δ₁ ⊕ Δ₂) ⊕ Δ₃ ) 
  assocᶜˡ _ _ _ (inj₁ c        , k) = (inj₁ (inj₁ c) , k)
  assocᶜˡ _ _ _ (inj₂ (inj₁ c) , k) = ((inj₁ (inj₂ c)) , k)
  assocᶜˡ _ _ _ (inj₂ (inj₂ c) , k) = (inj₂ c , k)

  ⊕-assoc : ∀ Δ₁ Δ₂ Δ₃ → (∀ {X} → ⟦ Δ₁ ⊕ (Δ₂ ⊕ Δ₃) ⟧ X ↔ ⟦ (Δ₁ ⊕ Δ₂) ⊕ Δ₃ ⟧ X)
  ⊕-assoc Δ₁ Δ₂ Δ₃ = record
    { to        = assocᶜˡ Δ₁ Δ₂ Δ₃
    ; from      = assocᶜʳ Δ₁ Δ₂ Δ₃
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   = (λ where refl → assoc-inverseˡ _) , (λ where refl → assoc-inverseʳ _) 
    }
    where
      assoc-inverseˡ : ∀ x → assocᶜˡ Δ₁ Δ₂ Δ₃ (assocᶜʳ Δ₁ Δ₂ Δ₃ x) ≡ x
      assoc-inverseˡ (inj₁ (inj₁ _) , _) = refl
      assoc-inverseˡ (inj₁ (inj₂ _) , _) = refl
      assoc-inverseˡ (inj₂ _        , _) = refl

      assoc-inverseʳ : ∀ x → assocᶜʳ Δ₁ Δ₂ Δ₃ (assocᶜˡ Δ₁ Δ₂ Δ₃ x) ≡ x
      assoc-inverseʳ (inj₁ _        , _) = refl
      assoc-inverseʳ (inj₂ (inj₁ _) , _) = refl
      assoc-inverseʳ (inj₂ (inj₂ _) , _) = refl

  ⊕-congʳ : ∀ Δ₁ Δ₂ Δ → (∀ {X} → ⟦ Δ₁ ⟧ X ↔ ⟦ Δ₂ ⟧ X) → (∀ {X} → ⟦ Δ ⊕ Δ₁ ⟧ X ↔ ⟦ Δ ⊕ Δ₂ ⟧ X)
  ⊕-congʳ Δ₁ Δ₂ Δ iso = record
    { to        = to′
    ; from      = from′
    ; to-cong   = λ where refl → refl
    ; from-cong = λ where refl → refl
    ; inverse   = (λ where refl → cong-inverseˡ _) , λ where refl → cong-inverseʳ _ 
    }
    where
      to′ : (Δ ⊕ Δ₁) ↦ (Δ ⊕ Δ₂)
      to′ (inj₁ c , k) = (inj₁ c , k)
      to′ (inj₂ c , k) = injʳ Δ (iso .to (c , k))

      from′ : (Δ ⊕ Δ₂) ↦ (Δ ⊕ Δ₁)
      from′ (inj₁ c , k) = (inj₁ c , k)
      from′ (inj₂ c , k) = injʳ Δ (iso .from (c , k))

      cong-inverseˡ : ∀ x → to′ (from′ x) ≡ x
      cong-inverseˡ (inj₁ x , k) = refl
      cong-inverseˡ (inj₂ y , k) = cong (injʳ Δ) (Inverse.inverse iso .proj₁ refl)

      cong-inverseʳ : ∀ x → from′ (to′ x) ≡ x 
      cong-inverseʳ (inj₁ x , k) = refl
      cong-inverseʳ (inj₂ y , k) = cong (injʳ Δ) (Inverse.inverse iso .proj₂ refl)

  instance
    unpack : ⦃ w : Δ ≲ Δ′ ⦄ → Δ ∙ proj₁ w ≈ Δ′
    unpack ⦃ w ⦄ = proj₂ w

  ≲-left : Δ ≲ (Δ ⊕ Δ′)
  ≲-left {Δ′ = Δ′} = Δ′ , record { reorder = ↔-id _ }

  ≲-right : ⦃ Δ ≲ Δ₂ ⦄ → Δ ≲ (Δ₁ ⊕ Δ₂)
  ≲-right {Δ} {Δ₂} {Δ₁} ⦃ x , record { reorder = reorder } ⦄ =
    (Δ₁ ⊕ _) , (record { reorder =
      ⊕-congʳ _ _ _ reorder
        ↔-∘ ( (↔-sym (⊕-assoc _ _ _)
              ↔-∘ ( ⊕-congˡ _ _ _ (⊕-comm _ _)
                    ↔-∘ ⊕-assoc _ _ _ )) ) })


  ∙-comm : Δ₁ ∙ Δ₂ ≈ Δ → Δ₂ ∙ Δ₁ ≈ Δ
  reorder (∙-comm record { reorder = re }) = re ↔-∘ ⊕-comm _ _

  ∙-refl : Δ₁ ∙ Δ₂ ≈ (Δ₁ ⊕ Δ₂)
  reorder ∙-refl = ↔-id _
\end{code}
%
A handler of type
\ad{⟨}~\ab{A}~\ad{!}~\ab{Δ}~\ad{⇒}~\ab{P}~\ad{⇒}~\ab{B}~\ad{!}~\ab{Δ′}~\ad{⟩} is
parameterized in the sense that it turns a computation of type
\ad{Free}~\ab{Δ}~\ab{A} into a parameterized computation of type
\ab{P}~\as{→}~\ad{Free}~\ab{Δ′}~\ab{B}.  The following function does so by
folding using \aF{ret}, \aF{hdl}, and a \ad{to-front} function:\footnote{The syntax \as{λ}~\ak{where}~$\ldots$ is a \emph{pattern-matching} lambda in Agda.  The function
  \af{flip} has the following type: \as{(}\ab{A}~\as{→}~\ab{B}~\as{→}~\ab{C}\as{)~→~(}\ab{B}~\as{→}~\ab{A}~\as{→}~\ab{C}\as{)}.}
%
\begin{code}[hide]
  from-front : ⦃ Δ₁ ∙ Δ₂ ≈ Δ ⦄ → Free (Δ₁ ⊕ Δ₂) A → Free Δ A
  from-front ⦃ w ⦄ = hmap-free (w .reorder .Inverse.to)
  module _ where
    open Inverse
\end{code}
\begin{code}
    to-front : ⦃ Δ₁ ∙ Δ₂ ≈ Δ ⦄ → Free Δ A → Free (Δ₁ ⊕ Δ₂) A
    to-front ⦃ w ⦄ = hmap-free (w .reorder .from)

    given_handle_  : ⦃ w : Δ₁ ∙ Δ₂ ≈ Δ ⦄
                   → ⟨ A ! Δ₁ ⇒ P ⇒ B ! Δ₂ ⟩ → Free Δ A → (P → Free Δ₂ B)
    given_handle_  h m = fold
      (ret h)
      ( λ where (inj₁ c , k) p → hdl h (c , k) p
                (inj₂ c , k) p → impure (c , flip k p) ) 
      (to-front m) 
\end{code}
%
Comparing with the syntax we used to explain algebraic effects and handlers in
the introduction, the \aF{ret} field corresponds to the $\Return{}$ case of the
handlers from the introduction, and \aF{hdl} corresponds to the cases that
define how operations are handled.  The parameterized handler type
\ad{⟨}~\ab{A}~\ad{!}~\ab{Δ}~\ad{⇒}~\ab{P}~\ad{⇒}~\ab{B}~\ad{!}~\ab{Δ′}~\ad{⟩}
corresponds to the type $\Typing{A}{Δ,Δ′} \Rightarrow P \to \Typing{B}{Δ′}$, and
\af{given}~\ab{h}~\af{handle}~\ab{m} corresponds to $\With{h}{m}$.

Using this type of handler, the $\Id{hOut}$ handler from the introduction can be defined as follows:
%
\begin{code}
  hOut : ⟨ A ! Output ⇒ ⊤ ⇒ (A × String) ! Δ ⟩
  ret hOut x _ = pure (x , "")
  hdl hOut (out s , k) p = do (x , s′) ← k tt p; pure (x , s ++ s′)
\end{code}
%
The handler $\Id{hOut}$ in \cref{sec:background} did not bind any parameters.
However, since we are encoding it as a \emph{parameterized} handler, \af{hOut}
now binds a unit-typed parameter.  Besides this difference, the handler is the
same as in \cref{sec:background}.  We can use the \af{hOut} handler to run
computations.  To this end, we introduce a \af{Nil} effect with no associated
operations which we will use to indicate where an effect row
ends:\\
\begin{minipage}{0.445\linewidth}
\begin{code}
  Nil : Effect
  Op   Nil = ⊥
  Ret  Nil = ⊥-elim
\end{code}
\begin{code}[hide]
  ∙-unitᵣ : Δ ∙ Nil ≈ Δ
  ∙-unitᵣ = record
    { reorder = record
      { to        = λ where (inj₁ c , k) → c , k
      ; from      = λ where (c , k) → inj₁ c , k
      ; to-cong   = λ where refl → refl
      ; from-cong = λ where refl → refl
      ; inverse   = (λ where refl → refl) , λ where {x = inj₁ c , k} refl → refl
      }
      }

  private instance ≲-refl' : Δ ≲ Δ
  ≲-refl' = Nil , ∙-unitᵣ 
\end{code}
\end{minipage}
\hfill\vline\hfill
\begin{minipage}{0.545\linewidth}
\begin{code}
  un : Free Nil A → A
  un (pure x) = x
\end{code}
\end{minipage}
\\
Using these, we can run a simple hello world program:\footnote{The \ac{refl} constructor is from the Agda standard library, and witnesses that a propositional equality (\ad{≡}) holds.}\\
\begin{minipage}{0.440\linewidth}
\begin{code}
  hello′ : ⦃ Output ≲ Δ ⦄ → Free Δ ⊤
  hello′ = do
    ‵out "Hello"; ‵out " world!"
\end{code}
\end{minipage}
\hfill\vline\hfill
\begin{minipage}{0.55\linewidth}
\begin{code}
  test-hello :  un (given hOut handle hello′ $ tt)
                ≡ (tt , "Hello world!")
  test-hello = refl
\end{code}
\end{minipage}
An example of parameterized (as opposed to unparameterized) handlers, is the state effect.
\Cref{fig:state-effect-handler} declares and illustrates how to handle such an effect with operations for reading (\ac{get}) and changing (\ac{put}) the state of a memory cell holding a natural number.
\\
\begin{figure}
\centering
\begin{minipage}{0.440\linewidth}
\begin{code}
  data StateOp : Set where
    get :      StateOp
    put : ℕ →  StateOp
\end{code}
\end{minipage}
\hfill\vline\hfill
\begin{minipage}{0.55\linewidth}
\begin{code}
  State : Effect
  Op State = StateOp
  Ret State get      = ℕ
  Ret State (put n)  = ⊤
\end{code}
\end{minipage}
\\
\begin{code}[hide]
  ‵put : ⦃ State ≲ Δ ⦄ → ℕ → Free Δ ⊤
  ‵put n = inject (impure ((put n) , pure)) 
  
  ‵get : ⦃ State ≲ Δ ⦄ → Free Δ ℕ
  ‵get = inject (impure (get , pure)) 
\end{code}
\hrulefill\\
\begin{code}
  hSt : ⟨ A ! State ⇒ ℕ ⇒ (A × ℕ) ! Δ′ ⟩
  ret hSt x s = pure (x , s)
  hdl hSt (put m , k) n = k tt  m
  hdl hSt (get   , k) n = k n   n

  ‵incr : ⦃ State ≲ Δ ⦄ → Free Δ ⊤
  ‵incr = do n ← ‵get; ‵put (n + 1)

  incr-test : un ((given hSt handle ‵incr) 0) ≡ (tt , 1)
  incr-test = refl
\end{code}
\begin{code}[hide]
  hSt′ : ⟨ A ! State ⇒ ⊤ ⇒ (ℕ → (Free Δ′ (A × ℕ))) ! Δ′ ⟩
  ret hSt′ x _ = pure (λ s → pure (x , s))
  hdl hSt′ (get , k) _ = pure (λ s → k s tt >>= λ f → f s)
  hdl hSt′ (put s′ , k) _ = pure (λ _ → k tt tt >>= λ f → f s′)
\end{code}
\caption{A state effect (upper), its handler (\af{hSt} below), and a simple test (\af{incr-test}, also below) which uses (the elided) smart constructors for \ac{get} and \ac{put}}
\label{fig:state-effect-handler}
\end{figure}


\subsection{The Modularity Problem with Higher-Order Effects, Revisited}
\label{sec:higher-order-effects}

\Cref{sec:modularity-problem} described the modularity problem with higher-order
effects, using a higher-order operation that interacts with output as an
example.  In this section we revisit the problem, framing it in terms of the
definitions introduced in the previous section.
To this end, we use a different effect whose
interface is summarized by the \ad{CatchM} record below.  The record asserts
that the computation type \ab{M}~\as{:}~\ad{Set}~\as{→}~\ad{Set} has at least a
higher-order operation \aF{catch} and a first-order operation \aF{throw}:
\begin{code}[hide]
module AlgebraicityProperty (M : Set → Set) (RM : RawMonad M) where
  open RawMonad RM
\end{code}
%
\begin{code}
  record CatchM (M : Set → Set) : Set₁ where
    field  catch  : M A → M A →  M A
           throw  :              M A
\end{code}
%
The idea is that \aF{throw} throws an exception, and \aF{catch}~\ab{m₁}~\ab{m₂}
handles any exception thrown during evaluation of \ab{m₁} by running \ab{m₂}
instead.  The problem is that we cannot give a modular definition of operations
such as \aF{catch} using algebraic effects and handlers alone.  As discussed in
\cref{sec:modularity-problem}, the crux of the problem is that algebraic effects
and handlers provide limited support for higher-order operations.  However, as
also discussed in \cref{sec:modularity-problem}, we can encode \af{catch} in
terms of more primitive effects and handlers, such as the following handler for
the \ad{Throw} effect:
%
\begin{code}[hide]
module Abbreviation where
  open FreeModule
  open ⟨_!_⇒_⇒_!_⟩
\end{code}
%
%
\begin{code}
  hThrow : ⟨ A ! Throw ⇒ ⊤ ⇒ (Maybe A) ! Δ′ ⟩
  ret  hThrow x _ = pure (just x)
  hdl  hThrow (throw , k) _ = pure nothing
\end{code}
%
The handler modifies the return type of the computation by decorating it with a
\ad{Maybe}.  If no exception is thrown, \aF{ret} wraps the yielded value in a
\ac{just} constructor.  If an exception is thrown, the handler never invokes the
continuation \ab{k} and aborts the computation by returning \ac{nothing}
instead.
%
We can elaborate \aF{catch} into an inline application of \af{hThrow}.  To do so
we make use of \emph{effect masking} which lets us ``weaken'' the type of a
computation by inserting extra effects in an effect row:
%
\begin{code}
  ♯_ : ⦃ Δ₁ ≲ Δ₂ ⦄ → Free Δ₁ A → Free Δ₂ A
\end{code}
\begin{code}[hide]
  ♯_ = inject 
\end{code}
%
Using this, the following elaboration defines a semantics for the \aF{catch} operation:\footnote{The \af{maybe} function is the eliminator for the \ad{Maybe} type.  Its first parameter is for eliminating a \ac{just}; the second  for \ac{nothing}.  Its type is \af{maybe}~\as{:}~\as{(}\ab{A}~\as{→}~\ab{B}\as{)}~\as{→}~\ab{B}~\as{→}~\ad{Maybe}~\ab{A}~\as{→}~\ab{B}.}
\footnote{The instance resolution machinery of Agda requires some help to resolve the instance argument of \af{♯} here.  We provide a hint to Agda's instance resolution machinery in an implicit instance argument that we omit for readability in the paper.  In the rest of this paper, we will occasionally follow the same convention.}
%
\begin{code}[hide]
  module _ ⦃ w : Throw ≲ Δ ⦄ where
\end{code}
\begin{code}
    catch : ⦃ Throw ≲⅋ Δ ⦄ → Free Δ A → Free Δ A → Free Δ A
    catch m₁ m₂ = (♯ (given hThrow handle m₁) tt) 𝓑 maybe pure m₂ 
\end{code}
\begin{code}[hide]
      where instance _ = _ , ∙-comm (w .proj₂)
\end{code}
%
If \ab{m₁} does not throw an exception, we return the produced value.  If it
does, \ab{m₂} is run.

As observed by \citet{WuSH14}, programs that use elaborations such as \af{catch}
are less modular than programs that only use plain algebraic operations.  In
particular, the effect row type of computations no longer represents the
interface of operations that we use to write programs, since the \ad{catch}
elaboration is not represented in the effect type at all.  So we have to rely on
different machinery if we want to refactor, optimize, or change the semantics of
\ad{catch} without having to change programs that use it.

In the next subsection we describe how to define effectful operations such as
\ad{catch} modularly using scoped effects and handlers, and discuss how this is
not possible for, e.g., operations representing $\lambda$-abstraction.


\subsection{Scoped Effects and Handlers}
\label{sec:scoped-effects}

\begin{code}[hide]
module Scoped where
  open FreeModule   using (Effect; State; put; get; Δ; Δ₁ ; Δ₂; Δ′; _≲_ ; _∙_≈_; throw; Throw; _⊕_; ⟦_⟧; Alg)
  open Effect

  private variable γ γ₁ γ₂ : Effect
                   n m : Level
                   X Y Z : Set n
                   H : Set n → Set m
\end{code}

This subsection gives an overview of scoped effects and handlers.  While the
rest of the paper can be read and understood without a deep understanding of
scoped effects and handlers, we include this overview to facilitate comparison
with the alternative solution that we introduce in
\cref{sec:hefty-trees-and-algebras}.

Scoped effects extend the expressiveness of algebraic effects to support a class
of higher-order operations that \citet{WuSH14,PirogSWJ18,YangPWBS22} call
\emph{scoped operations}. We illustrate how scoped effects work, using a freer
monad encoding of the endofunctor algebra approach of~\citet{YangPWBS22}.  The
work of \citet{YangPWBS22} does not include examples of modular handlers, but
the original paper on scoped effects and handlers by \citet{WuSH14} does.  We
describe an adaptation of the modular handling techniques due to \citet{WuSH14}
to the endofunctor algebra approach of \citet{YangPWBS22}.


\subsubsection{Scoped Programs}
\label{sec:scoped-programs}
%
Scoped effects extend the free monad data type with an additional row for scoped
operations.  The \ac{return} and \ac{call} constructors of \ad{Prog} below
correspond to the \ac{pure} and \ac{impure} constructors of the free monad,
whereas \ac{enter} is new:
%
\begin{code}
  data Prog (Δ γ : Effect) (A : Set) : Set where
    return  : A                              → Prog Δ γ A
    call    : ⟦ Δ ⟧ (Prog Δ γ A)             → Prog Δ γ A
    enter   : ⟦ γ ⟧ (Prog Δ γ (Prog Δ γ A))  → Prog Δ γ A
\end{code}
%
Here, the \ac{enter} constructor represents a higher-order operation with
\emph{sub-scopes}; i.e., computations that themselves return computations:
%
\begin{equation*}
  \underbrace{\ad{Prog}~\ab{Δ}~\ab{γ}}_{\textrm{outer}}~\as{(}\underbrace{\ad{Prog}~\ab{Δ}~\ab{γ}}_{\textrm{inner}}~\ab{A}\as{)}
\end{equation*}
%
This type represents \emph{scoped} computations in the sense that outer
computations can be handled independently of inner ones, as we illustrate in \cref{sec:scoped-effect-handlers}.
One way to think of inner computations is as continuations (or join-points) of sub-scopes.

\begin{code}[hide]
  {-# TERMINATING #-} 
  map-prog : (A → B) → Prog Δ γ A → Prog Δ γ B
  map-prog f (return x) = return (f x)
  map-prog f (call (op , k)) = call (op , (λ x → map-prog f (k x)))
  map-prog f (enter (op , k)) = enter (op , λ x → map-prog (map-prog f) (k x))
  
  {-# TERMINATING #-} 
  _𝓑_ : Prog Δ γ A → (A → Prog Δ γ B) → Prog Δ γ B
  return x       𝓑 g = g x
  call  (op , k) 𝓑 g = call  (op , (λ x → k x 𝓑 g))
  enter (op , k) 𝓑 g = enter (op , (λ x → map-prog (λ t → t 𝓑 g) (k x)))
\end{code}

Using \ad{Prog}, the catch operation can be defined as a scoped operation:
%
\begin{minipage}{0.495\linewidth}
\begin{code}
  data CatchOp : Set where
    catch : CatchOp
\end{code}
\end{minipage}
\hfill\vline\hfill
\begin{minipage}{0.495\linewidth}
\begin{code}
  Catch : Effect
  Op   Catch = CatchOp
  Ret  Catch catch = Bool
\end{code}
\end{minipage}
%
The effect signature indicates that \af{Catch} has two scopes since \ad{Bool}
has two inhabitants.
%
\begin{code}[hide]
  ‵catch : ⦃ Catch ≲ γ ⦄ → Prog Δ γ A → Prog Δ γ A → Prog Δ γ A
  ‵catch ⦃ w ⦄ m₁ m₂ =
    enter (w .proj₂ ._∙_≈_.reorder .Inverse.to (inj₁ catch , λ b → if b then return m₁ else return m₂)) 
\end{code}
%
Following~\citet{YangPWBS22}, scoped operations are handled using a structure-preserving fold over \ad{Prog}:
\\
\begin{minipage}{0.375\linewidth}
\begin{code}[hide]
  CallAlg : (Δ : Effect) (G : Set → Set) → Set₁
  CallAlg Δ G = {A : Set} → ⟦ Δ ⟧ (G A) → G A 
 
  EnterAlg : (γ : Effect) (G : Set → Set) → Set₁
  EnterAlg γ G = {A : Set} → ⟦ γ ⟧ (G (G A)) → G A

  {-# TERMINATING #-} 
\end{code}
\begin{code}
  hcata  :  (∀ {X} → X → G X) 
         →  CallAlg   Δ  G
         →  EnterAlg  γ  G
         →  Prog Δ γ A → G A
\end{code}
\begin{code}[hide]
  hcata gen f g (return x) = gen x
  hcata gen f g (call (op , k)) = f (op , hcata gen f g ∘ k)
  hcata gen f g (enter (op , k)) = g (op , hcata gen f g ∘ map-prog (hcata gen f g) ∘ k)

  hmap-prog : (∀ {X} → ⟦ Δ₁ ⟧ X → ⟦ Δ₂ ⟧ X) → Prog Δ₁ γ A → Prog Δ₂ γ A
  hmap-prog f = hcata return (call ∘ f) enter 

  hmap-prog′ : (∀ {X} → ⟦ γ₁ ⟧ X → ⟦ γ₂ ⟧ X) → Prog Δ γ₁ A → Prog Δ γ₂ A
  hmap-prog′ f = hcata return call (enter ∘ f)

  ⊕[_,_] : Alg Δ₁ A → Alg Δ₂ A → Alg (Δ₁ ⊕ Δ₂) A 
  ⊕[ a , b ] (inj₁ c , k) = a (c , k)
  ⊕[ a , b ] (inj₂ c , k) = b (c , k)

  ⊕[_,_]′ : EnterAlg γ₁ F → EnterAlg γ₂ F → EnterAlg (γ₁ ⊕ γ₂) F
  ⊕[ a , b ]′ (inj₁ c , k) = a (c , k)
  ⊕[ a , b ]′ (inj₂ c , k) = b (c , k)
\end{code}
\end{minipage}
\hfill\vline\hfill
\begin{minipage}{0.615\linewidth}
\begin{code}
  CallAlg⅋ : (Δ : Effect) (G : Set → Set) → Set₁
  CallAlg⅋ Δ G  =
    {A : Set} → ⟦ Δ ⟧ (G A) → G A

  EnterAlg⅋ : (γ : Effect) (G : Set → Set) → Set₁
  EnterAlg⅋ γ G  =
    {A B : Set} → ⟦ γ ⟧ (G (G A)) → G A 
\end{code}
\end{minipage}
%
The first argument represents the case where we are folding a \ac{return} node;
the second and third correspond to respectively \ac{call} and \ac{enter}.

\subsubsection{Scoped Effect Handlers}
\label{sec:scoped-effect-handlers}
%
The following defines a type of parameterized scoped effect handlers:
%
\begin{code}
  record ⟨∙!_!_⇒_⇒_∙!_!_⟩  (Δ γ : Effect)   (P : Set) (G : Set → Set)
                           (Δ′ γ′ : Effect) : Set₁ where
    field  ret     :  X → P → Prog Δ′ γ′ (G X)
           hcall   :  CallAlg   Δ  (λ X → P → Prog Δ′ γ′ (G X))
           henter  :  EnterAlg  γ  (λ X → P → Prog Δ′ γ′ (G X))
           glue    :  (k : C → P → Prog Δ′ γ′ (G X)) (r : G C) → P → Prog Δ′ γ′ (G X)
\end{code}
\begin{code}[hide]
  open ⟨∙!_!_⇒_⇒_∙!_!_⟩
  open _∙_≈_
  open Inverse 

  to-frontΔ : ⦃ w : Δ₁ ∙ Δ₂ ≈ Δ ⦄ → Prog Δ γ A → Prog (Δ₁ ⊕ Δ₂) γ A
  to-frontΔ ⦃ w ⦄ x = hmap-prog (w .reorder .from) x

  to-frontγ : ⦃ w : γ₁ ∙ γ₂ ≈ γ ⦄ → Prog Δ γ A → Prog Δ (γ₁ ⊕ γ₂) A
  to-frontγ ⦃ w ⦄ x = hmap-prog′ (w .reorder .from) x
\end{code}
%
A handler of type
\ad{⟨∙}~\ad{!}~\ab{Δ}~\ad{!}~\ab{γ}~\ad{⇒}~\ab{P}~\ad{⇒}~\ab{G}~\ad{∙!}~\ab{Δ′}~\ad{!}~\ab{γ}~\ad{⟩}
handles operations of \ab{Δ} and \ab{γ} \emph{simultaneously} and turns a
computation \ad{Prog}~\ab{Δ~γ~A} into a parameterized computation of type
\ab{P}~\as{→}~\ad{Prog}~\ab{Δ′}~\ab{γ′}~\as{(}\ab{G}~\ab{A}\as{)}.  The \aF{ret}
and \aF{hcall} cases are similar to the \aF{ret} and \aF{hdl} cases from
\cref{sec:effect-handlers}.  The crucial addition which adds support for
higher-order operations is the \aF{henter} case.

The \aF{henter} field is given by an \af{EnterAlg} case.  This case takes as
input a scoped operation whose outer and inner computation have been folded into a parameterized computation of type \ab{P}~\as{→}~\ad{Prog}~\ab{Δ′}~\ab{γ′}~\as{(}\ab{G~X}\as{)}; and returns as output an interpretation of that operation as a computation of type \ab{P}~\as{→}~\ad{Prog}~\ab{Δ′}~\ab{γ′}~\as{(}\ab{G~X}\as{)}.
The \aF{glue} function is used for modularly \emph{weaving}~\citep{WuSH14} side effects of handlers
through sub-scopes of yet-unhandled operations.


\subsubsection{Weaving}
\label{sec:weaving}
%
To see why \aF{glue} is needed, it is instructional to look at how the fields in
the record type above are used to fold over \ad{Prog}:
%
\begin{code}
  given_handle-scoped_  :  ⦃ w₁ : Δ₁ ∙ Δ₂ ≈ Δ ⦄ ⦃ w₂ : γ₁ ∙ γ₂ ≈ γ ⦄
                        →  ⟨∙! Δ₁ ! γ₁ ⇒ P ⇒ G ∙! Δ₂ ! γ₂ ⟩
                        →  Prog Δ γ A → P → Prog Δ₂ γ₂ (G A)
  given h handle-scoped m = hcata (ret h)
    ⊕[ hcall h
     , (λ where (c , k) p → call (c , flip k p)) ]
    ⊕[ (λ {A} → henter h {A})
     , (λ where (c , k) p → enter (c , λ x → map-prog (λ y → glue h id y p) (k x p))) ]′
     (to-frontΔ (to-frontγ m))
\end{code}
%
The second to last line above shows how \aF{glue} is used.  Because \af{hcata}
eagerly folds the current handler over scopes (\ab{sc}), there is a mismatch
between the type that the continuation expects (\ab{B}) and the type that the
scoped computation returns (\ab{G}~\ab{B}).  The \aF{glue} function fixes this
mismatch for the particular return type modification
\ab{G}~\as{:}~\ad{Set}~\as{→}~\ad{Set} of a parameterized scoped effect handler.

The scoped effect handler for exception catching is thus:
%
\begin{code}
  hCatch  :  ⟨∙! Throw ! Catch ⇒ ⊤ ⇒ Maybe ∙! Δ ! γ ⟩
  ret     hCatch x _ = return (just x)
  hcall   hCatch (throw , k) _ = return nothing
  henter  hCatch (catch , k) _ = let m₁ = k true
                                     m₂ = k false in
      m₁ tt 𝓑 λ where
        (just f)  → f tt
        nothing   → m₂ tt 𝓑 maybe (_$ tt) (return nothing)
  glue hCatch k x _ = maybe (flip k tt) (return nothing) x
\end{code}
%
The \aF{henter} field for the \ac{catch} operation first runs \ab{m₁}.  If no
exception is thrown, the value produced by \ab{m₁} is forwarded to \ab{k}.
Otherwise, \ab{m₂} is run and its value is forwarded to \ab{k}, or its exception
is propagated.  The \aF{glue} field of \af{hCatch} says that, if an unhandled
exception is thrown during evaluation of a scope, the continuation is discarded
and the exception is propagated; and if no exception is thrown the continuation
proceeds normally.


\subsubsection{Discussion and Limitations}
\label{sec:scoped-discussion}
%
As observed by \citet{BergSPW21}, some higher-order effects do not correspond to
scoped operations.  In particular, the \ad{LambdaM} record shown below is not a scoped operation:
%
\begin{code}
  record LambdaM (V : Set) (M : Set → Set) : Set₁ where
    field  lam : (V → M V)  → M V
           app : V → M V    → M V
\end{code}
%
The \aF{lam} field represents an operation that constructs a $\lambda$ value.
The \aF{app} field represents an operation that will apply the function value in
the first parameter position to the argument computation in the second parameter
position.  The \aF{app} operation has a computation as its second parameter so
that it remains compatible with different evaluation strategies.

To see why the operations summarized by the \ad{LambdaM} record above are not
scoped operations, let us revisit the \ac{enter} constructor of \ad{Prog}:
%
\begin{equation*}
  \ac{enter}~\as{:~}\af{⟦}~\ab{γ}~\af{⟧}~\as{(}\underbrace{\ad{Prog}~\ab{Δ}~\ab{γ}}_{\textrm{outer}}~\as{(}\underbrace{\ad{Prog}~\ab{Δ}~\ab{γ}}_{\textrm{inner}}~\ab{A}\as{))}~\as{→}~\ad{Prog}~\ab{Δ}~\ab{γ}~\ab{A}
\end{equation*}
%
As summarized earlier in this subsection, \ac{enter} lets us represent
higher-order operations (specifically, \emph{scoped operations}), whereas
\ac{call} does not (only \emph{algebraic operations}).  Just like we defined the
computational parameters as scopes (given by the outer \ad{Prog} in the type of
\ac{enter}), we might try to define the body of a lambda as a scope in a similar
way.  However, whereas the \ac{catch} operation always
passes control to its continuation (the inner \ad{Prog}), the \aF{lam} effect is
supposed to package the body of the lambda into a value and pass this value to
the continuation (the inner computation).  Because the inner computation is
nested within the outer computation, \emph{the only way to gain access to the
inner computation (the continuation) is by first running the outer computation
(the body of the lambda)}.  This does not give us the right semantics.

It is possible to elaborate the \ad{LambdaM} operations into more primitive
effects and handlers, but as discussed in
\cref{sec:modularity-problem,sec:higher-order-effects}, such elaborations are
not modular.
In the next section we show how to make such elaborations modular.

%%% Local Variables:
%%% reftex-default-bibliography: ("../references.bib")
%%% End:




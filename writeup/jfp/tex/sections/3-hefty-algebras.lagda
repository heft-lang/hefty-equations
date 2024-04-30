\begin{code}[hide]
{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module tex.sections.3-hefty-algebras where

open import tex.sections.2-algebraic-effects

open import Function hiding (_⟨_⟩_)
open import Level hiding (Lift)
open import Agda.Primitive
open import Data.Empty
open import Data.Unit
open import Data.Bool hiding (T)
open import Data.Sum
open import Data.Product
open import Data.Maybe hiding (_>>=_)
open import Data.Nat hiding (_⊔_)
open import Data.Integer using (ℤ)
open import Data.String
open import Data.List hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open import Relation.Unary using (IUniversal ; _⇒_)

open import Data.String

open Abbreviation using (hThrow; ♯_)

\end{code}

\section{Hefty Trees and Algebras}
\label{sec:hefty-trees-and-algebras}

\newcommand{\Mat}[1]{\mathrm{#1}}

As observed in \cref{sec:higher-order-effects}, operations such as \ad{catch}
can be elaborated into more primitive effects and handlers.  However, these
elaborations are not modular.  We solve this problem by factoring
elaborations into interfaces of their own to make them modular.

To this end, we first introduce a new type of abstract syntax trees
(\cref{sec:towards-hefty-trees,sec:lifting-algebraic-to-higher-order,sec:hefty-monadic-bind})
representing computations with higher-order operations, which we dub \emph{hefty
  trees} (an acronymic pun on \emph{h}igher-order \emph{ef}fec\emph{t}s).  We
then define elaborations as algebras (\emph{hefty algebras};
\cref{sec:hefty-algebras}) over these trees.  The following pipeline summarizes
the idea, where \ab{H} is a \emph{higher-order effect signature}:
%
\begin{equation*}
  \ad{Hefty}~\ab{H}~\ab{A}
  \xrightarrow{\Id{elaborate}} \ad{Free}~\ab{Δ}~\ab{A}
  \xrightarrow{\Id{handle}} \Id{Result}
\end{equation*}

For the categorically inclined reader, \ad{Hefty} conceptually corresponds to
the initial algebra of the functor $\Id{HeftyF}~H~A~R = A + H~R~(R~A)$ where
$H : (\ad{Set} \to \ad{Set}) \to (\ad{Set} \to \ad{Set})$ defines the signature
of higher-order operations and is a \emph{higher-order functor}, meaning we have
both the usual functorial $\Id{map} : (X \to Y) \to H~F~X \to H~F~Y$ for any
functor $F$ as well as a function
$\Id{hmap} : \Mat{Nat}(F, G) \to \Mat{Nat}(H~F, H~G)$ which lifts natural
transformations between any $F$ and $G$ to a natural transformation between
$H~F$ and $H~G$.  A hefty algebra is then an $F$-algebra over a higher-order
signature functor $H$.  The notion of elaboration that we introduce in
\cref{sec:hefty-algebras} is an $F$-algebra whose carrier is a ``first-order''
effect tree (\ad{Free}~\ab{Δ}).

In this section, we encode this conceptual framework in Agda using a
container-inspired approach to represent higher-order signature functors $H$ as
a strictly positive type.  We discuss and compare our approach with previous
work in \cref{sec:limitations}.


\subsection{Generalizing \ad{Free} to Support Higher-Order Operations}
\label{sec:towards-hefty-trees}

\begin{code}[hide]
module HeftyModule where
  open FreeModule hiding (_𝓑_; _>>_) renaming (‵throw to ‵throw₀)
\end{code}

As summarized in \cref{sec:free-monad}, \ad{Free}~\ab{Δ}~\ab{A} is the type of
abstract syntax trees representing computations over the effect signature
\ab{Δ}.  Our objective is to arrive at a more general type of abstract syntax
trees representing computations involving (possibly) higher-order operations.
To realize this objective, let us consider how to syntactically represent this
variant of the $\Id{censor}$ operation (\cref{sec:modularity-problem}), where
\ab{M} is the type of abstract syntax trees whose type we wish to define:
%
\begin{flalign*}
   \;\;\af{censorₒₚ}~\as{:~(}\ad{String}~\as{→}~\ad{String}\as{)~→}~\ab{M}~\ad{⊤}~\as{→}~\ab{M}~\ad{⊤}
  &&
\end{flalign*}
%
We call the second parameter of this operation a \emph{computation parameter}.
Using \ad{Free}, computation parameters can only be encoded as continuations.
But the computation parameter of \af{censorₒₚ} is \emph{not} a continuation, since
%
\begin{equation*}
  \ak{do}~\as{(}\af{censorₒₚ}~~\ab{f}~~\ab{m}\as{);}~\af{‵out}~\ab{s}~~\not\equiv~~\af{censorₒₚ}~~\ab{f}~~\as{(}\ak{do}~\ab{m}\as{;}~\af{‵out}~\ab{s}\as{)}.
\end{equation*}
%
The crux of the issue is how signature functors \af{⟦}~\ab{Δ}~\af{⟧}~\as{:}~\ad{Set}~\as{→}~\ad{Set} are defined.
Since this is an endofunctor on \ad{Set}, the only suitable option in the \ac{impure} constructor is to apply the functor to the type of \emph{continuations}:
%
\begin{equation*}
  \ac{impure}~\as{:~}\af{⟦}~\ab{Δ}~\af{⟧}~\as{(}\underbrace{\ad{Free}~\ab{Δ}~\ab{A}}_{\textrm{continuation}}\as{)}~\as{→}~\ad{Free}~\ab{Δ}~\ab{A}
\end{equation*}
%
A more flexible approach would be to allow signature functors to build computation trees with an \emph{arbitrary return type}, including the return type of the continuation.
A \emph{higher-order} signature functor of some higher-order signature \ab{H}, written \af{⟦}~\ab{H}~\af{⟧ᴴ}~\as{:}~\as{(}\ad{Set}~\as{→}~\ad{Set}\as{)~→}~\ad{Set}~\as{→}~\ad{Set}, would fit that bill.
Using such a signature functor, we could define the \ac{impure} case as follows:
%
\begin{equation*}
  \ac{impure}~\as{:}~\af{⟦}~\ab{H}~\af{⟧ᴴ}~\as{(}\underbrace{\ad{Hefty}~\ab{H}}_{\begin{array}{c}\text{\footnotesize computation}\\[-0.5em]\text{\footnotesize type}\end{array}}\as{)}~\overbrace{\ab{A}}^{\begin{array}{c}\text{\footnotesize continuation}\\[-0.5em]\text{\footnotesize return type}\end{array}}~\as{→}~\ad{Hefty}~\ab{H}~\ab{A}
\end{equation*}
%
Here, \ad{Hefty} is the type of the free monad using higher-order signature functors instead.
In the rest of this subsection, we consider how to define higher-order signature functors \ab{H}, their higher-order functor extensions \af{⟦\_⟧ᴴ}, and the type of \ad{Hefty} trees.

Recall how we defined plain algebraic effects in terms of \emph{containers}:
%
\begin{code}
  record Effect⅋ : Set₁ where
    field  Op⅋   : Set
           Ret⅋  : Op⅋ → Set
\end{code}
%
Here, \aF{Op} is the type of operations, and \aF{Ret} defines the return type of each operation.
In order to allow operations to have sub-computations, we generalize this type to allow each operation to be associated with a number of sub-computations, where each sub-computation can have a different return type.
The following record provides this generalization:
%
\begin{code}
  record Effectᴴ : Set₁ where
    field  Opᴴ     : Set                             -- As before
           Retᴴ    : Opᴴ → Set                       -- As before
           Fork    : Opᴴ → Set                       -- New
           Ty      : {op : Opᴴ} (ψ : Fork op) → Set  -- New
\end{code}
%
The set of operations is still given by a type field (\aF{Opᴴ}), and each operation still has a return type (\aF{Retᴴ}).
\aF{Fork} associates each operation with a type that indicates how many sub-computations (or \emph{forks}) an operation has, and \aF{Ty} indicates the return type of each such fork.
For example, say we want to encode an operation \ab{op} with two sub-computations with different return types, and whose return type is of a unit type.
That is, using \ab{M} as our type of computations:
%
\begin{equation*}
  \ab{op}~\as{:}~\ab{M}~\ad{ℤ}~\as{→}~\ab{M}~\ad{ℕ}~\as{→}~\ab{M}~\ad{⊤}
\end{equation*}
%
The following signature declares a higher-order effect signature with a single operation with return type \ad{⊤}, and with two forks (we use \ad{Bool} to encode this fact), and where each fork has, respectively \ad{ℤ} and \ad{ℕ} as return types.
%
\begin{code}[hide]
  open Effect
  open Effectᴴ
\end{code}
\begin{code}
  example-op : Effectᴴ
  Opᴴ   example-op        = ⊤     -- A single operation
  Retᴴ  example-op tt     = ⊤     -- with return type ⊤
  Fork  example-op tt     = Bool  -- with two forks
  Ty    example-op false  = ℤ     -- one fork has return type ℤ
  Ty    example-op true   = ℕ     -- the other has return type ℕ
\end{code}
%
The extension of higher-order effect signatures implements the intuition explained above:
%
\begin{code}
  ⟦_⟧ᴴ : Effectᴴ → (Set → Set) → Set → Set
  ⟦ H ⟧ᴴ M X = Σ (Opᴴ H) λ op → (Retᴴ H op → M X) × ((ψ : Fork H op) → M (Ty H ψ))

  map-sigᴴ : ∀ {H F G} → ∀[ F ⇒ G ] → ∀[ ⟦ H ⟧ᴴ F ⇒ ⟦ H ⟧ᴴ G ]
  map-sigᴴ θ (op , k , s) = op , θ ∘ k , θ ∘ s 
\end{code}
%
Let us unpack this definition.
%
\begin{equation*}
% \af{⟦}~\ab{H}~\af{⟧}~\overbrace{\ab{M}}^{computation types}~\ab{X}~\as{=}~
  \underbrace{\ad{Σ}~\as{(}~\aF{Opᴴ}~\ab{H}\as{)~λ}~\ab{op}~\as{→}}_{(1)}\as{~(}\underbrace{\aF{Retᴴ}~\ab{H}~\ab{op}~\as{→~}\ab{M}~\ab{X}}_{(2)}\as{)}~\ad{×}~\as{(}\underbrace{\as{(}\ab{ψ}~\as{:}~\aF{Fork}~\ab{H}~\ab{op}\as{)}}_{(3)}\as{~→}~\underbrace{\ab{M}~\as{(}\aF{Ty}~\ab{H}~\ab{ψ}\as{)}}_{(4)}\as{)}
\end{equation*}
%
The extension of a higher-order signature functor is given by (1) the sum of operations of the signature, where each operation has (2) a continuation (of type \ab{M}~\ab{X}) that expects to be passed a value of the operation's return type, and (3) a set of forks where each fork is (4) a computation that returns the expected type for each fork.

Using the higher-order signature functor and its extension above, our generalized free monad becomes:
%
\begin{code}
  data Hefty (H : Effectᴴ) (A : Set) : Set where
    pure    : A → Hefty H A
    impure  : ⟦ H ⟧ᴴ (Hefty H) A → Hefty H A
\end{code}
%
\begin{code}[hide]
  variable H H′ H″ H‴ H₀ H₁ H₂ H₃ H₄ : Effectᴴ

  variable
    m n : Level
    A B C D Z : Set n
    F F₀ F₁ F₂ F₃ G : Set n → Set (n ⊔ m)
\end{code}
\begin{code}[hide]
  infixr 12 _∔_

  _∔_ : Effectᴴ → Effectᴴ → Effectᴴ
  Opᴴ (H₁ ∔ H₂) = Opᴴ H₁ ⊎ Opᴴ H₂
  Retᴴ (H₁ ∔ H₂) = [ Retᴴ H₁ , Retᴴ H₂ ]
  Fork (H₁ ∔ H₂) = [ Fork H₁ , Fork H₂ ]
  Ty (H₁ ∔ H₂) {inj₁ _} ψ = Ty H₁ ψ
  Ty (H₁ ∔ H₂) {inj₂ _} ψ = Ty H₂ ψ
\end{code}
%
This type of \ad{Hefty} trees can be used to define higher-order operations with
an arbitrary number of computation parameters, with arbitrary return types.
Using this type, and using a co-product for higher-order effect signatures
(\af{\_∔\_}) which is analogous to the co-product for algebraic effect
signatures in \cref{sec:row-insertion}, \cref{fig:censor} represents the syntax
of the \ad{censorₒₚ} operation.
% 
\begin{figure}
\centering
\begin{minipage}{0.445\linewidth}
\begin{code}
  data CensorOp : Set where
    censor  :  (String → String)
            →  CensorOp
\end{code}
\end{minipage}
\hfill\vline\hfill
\begin{minipage}{0.545\linewidth}
\begin{code}
  Censor : Effectᴴ
  Opᴴ    Censor                 = CensorOp
  Retᴴ   Censor (censor f)      = ⊤
  Fork   Censor (censor f)      = ⊤
  Ty     Censor {censor f} tt   = ⊤
\end{code}
\end{minipage}
\\
\hrulefill\\
\begin{code}
  censorₒₚ : (String → String) → Hefty (Censor ∔ H) ⊤ → Hefty (Censor ∔ H) ⊤
  censorₒₚ f m = impure (inj₁ (censor f) , (λ where tt → m) , pure)
\end{code}
%
\caption{A higher-order censor effect and operation, with a single computation
  parameter (declared with \aF{Op}~\as{=}~\ad{⊤} in the effect signature top
  right) with return type \ad{⊤} (declared with \aF{Ret}~\as{=~λ~\_~→}~\ad{⊤}
  top right)}
\label{fig:censor}
\end{figure}

Just like \ad{Free}, \ad{Hefty} trees can be sequenced using monadic bind.
Unlike for \ad{Free}, the monadic bind of \ad{Hefty} is not expressible in terms
of the standard fold over \ad{Hefty} trees.  The difference between \ad{Free}
and \ad{Hefty} is that \ad{Free} is a regular data type whereas \ad{Hefty} is a
\emph{nested datatype}~\cite{DBLP:journals/fac/BirdP99}.  The fold of a nested
data type is limited to describe \emph{natural transformations}.  As
\citet{DBLP:journals/fac/BirdP99} show, this limitation can be overcome by using
a \emph{generalized fold}, but for the purpose of this paper it suffices to
define monadic bind as a recursive function:
%
\begin{code}
  _𝓑_ : Hefty H A → (A → Hefty H B) → Hefty H B
  pure x               𝓑 g = g x
  impure (op , k , s)  𝓑 g = impure (op , (_𝓑 g) ∘ k , s)
\end{code}
\begin{code}[hide]
  _>>_ : Hefty H A → Hefty H B → Hefty H B
  m₁ >> m₂ = m₁ 𝓑 λ _ → m₂

  hmap : (A → B) → Hefty H A → Hefty H B
  hmap f (pure x)               = pure (f x)
  hmap f (impure (op , k , s))  = impure (op , hmap f ∘ k , s)
\end{code}
%
The bind behaves similarly to the bind for \ad{Free}; i.e., \ab{m}~\af{𝓑}~\ab{g}
concatenates \ab{g} to all the leaves in the continuations (but not computation
parameters) of \ab{m}.

In \cref{sec:hefty-algebras} we show how to modularly elaborate higher-order
operations into more primitive algebraic effects and handlers (i.e.,
computations over \ad{Free}), by folding modular elaboration algebras
(\emph{hefty algebras}) over \ad{Hefty} trees.  First, we show (in
\cref{sec:lifting-algebraic-to-higher-order}) how \ad{Hefty} trees support
programming against an interface of both algebraic and higher-order operations.
We also address (in \cref{sec:hefty-monadic-bind}) the question of how to encode
effect signatures for higher-order operations whose computation parameters have
polymorphic return types, such as the highlighted \colorbox{gray!30}{\ab{A}}
below:
\begin{flalign*}
  \;\;\af{‵catch}~\as{:}~\ad{Hefty}~\ab{H}~\colorbox{gray!30}{\ab{A}}~\as{→}~\ad{Hefty}~\ab{H}~\colorbox{gray!30}{\ab{A}}~\as{→}~\ad{Hefty}~\ab{H}~\colorbox{gray!30}{\ab{A}}
\end{flalign*}


\subsection{Programs with Algebraic and Higher-Order Effects}
\label{sec:lifting-algebraic-to-higher-order}

Any algebraic effect signature can be lifted to a higher-order effect signature
with no fork (i.e., no computation parameters):
%
\begin{code}
  Lift : Effect → Effectᴴ
  Opᴴ   (Lift Δ) = Op Δ
  Retᴴ  (Lift Δ) = Ret Δ
  Fork  (Lift Δ) = λ _ → ⊥
  Ty    (Lift Δ) = λ()
\end{code}
%
Using this effect signature, and using higher-order effect row insertion
witnesses analogous to the ones we defined and used in \cref{sec:row-insertion},
the following smart constructor lets us represent any algebraic operation as a
\ad{Hefty} computation:
%
\begin{code}[hide]
  record _∙_≋_ (H₁ H₂ H : Effectᴴ) : Set₁ where
    field
      reorder : ∀ {M X} → ⟦ H₁ ∔ H₂ ⟧ᴴ M X ↔ ⟦ H ⟧ᴴ M X

  _≲ᴴ_ : (H₁ H₂ : Effectᴴ) → Set₁
  H₁ ≲ᴴ H₂ = ∃ λ H → H₁ ∙ H ≋ H₂ 

  postulate ≲ᴴ-refl  : H ≲ᴴ H 
  postulate ≲ᴴ-trans : H₁ ≲ᴴ H₂ → H₂ ≲ᴴ H₃ → H₁ ≲ᴴ H₃
\end{code}
%
\begin{code}[hide]
  open _∙_≋_

  injᴴˡ : ∀ {M X} → ⟦ H₁ ⟧ᴴ M X → ⟦ H₁ ∔ H₂ ⟧ᴴ M X
  injᴴˡ (op , k , s) = inj₁ op , k , s
  
  injᴴ : ⦃ H₁ ≲ᴴ H₂ ⦄ → ∀ {M X} → ⟦ H₁ ⟧ᴴ M X → ⟦ H₂ ⟧ᴴ M X  
  injᴴ {H₂ = _} ⦃ w ⦄ {M} {X} x = w .proj₂ .reorder {M = M} {X = X} .Inverse.to (injᴴˡ {M = M} {X = X} x)
  
--   inj▹ₗ  :  ⦃ H ∼ H₀ ▹ H′ ⦄ → Opᴴ H₀  → Opᴴ H
--   inj▹ᵣ  :  ⦃ H ∼ H₀ ▹ H′ ⦄ → Opᴴ H′  → Opᴴ H
-- 
--   inj▹ₗ ⦃ insert ⦄  = inj₁
--   inj▹ₗ ⦃ sift p ⦄  = inj₂ ∘ inj▹ₗ ⦃ p ⦄
-- 
--   inj▹ᵣ ⦃ insert ⦄  = inj₂
--   inj▹ᵣ ⦃ sift p ⦄  = [ inj₁ , inj₂ ∘ inj▹ᵣ ⦃ p ⦄ ]
-- 
-- 
--   inj▹ₗ-ret≡ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ (op : Opᴴ H₀)
--              → Retᴴ H (inj▹ₗ op) ≡ Retᴴ H₀ op
--   inj▹ₗ-ret≡ ⦃ insert ⦄ _  = refl
--   inj▹ₗ-ret≡ ⦃ sift p ⦄    = inj▹ₗ-ret≡ ⦃ p ⦄
-- 
--   inj▹ᵣ-ret≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ (op : Opᴴ H′)
--             → Retᴴ H (inj▹ᵣ op) ≡ Retᴴ H′ op
--   inj▹ᵣ-ret≡ ⦃ insert ⦄ op  = refl
--   inj▹ᵣ-ret≡ ⦃ sift p ⦄     = [ (λ _ → refl) , inj▹ᵣ-ret≡ ⦃ p ⦄ ]
-- 
--   inj▹ₗ-fork≡ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ (op : Opᴴ H₀)
--                 → Fork H (inj▹ₗ op) ≡ Fork H₀ op
--   inj▹ₗ-fork≡ ⦃ insert ⦄ _  = refl
--   inj▹ₗ-fork≡ ⦃ sift p ⦄    = inj▹ₗ-fork≡ ⦃ p ⦄
-- 
--   inj▹ᵣ-fork≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ (op : Opᴴ H′)
--                 → Fork H (inj▹ᵣ op) ≡ Fork H′ op
--   inj▹ᵣ-fork≡ ⦃ insert ⦄ op  = refl
--   inj▹ᵣ-fork≡ ⦃ sift p ⦄     = [ (λ _ → refl) , inj▹ᵣ-fork≡ ⦃ p ⦄ ]
-- 
--   inj▹ₗ-prong≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ {op : Opᴴ H₀} (b : Op (Fork H (inj▹ₗ op)))
--                 → Ret (Fork H (inj▹ₗ op)) b ≡ Ret (Fork H₀ op) (subst Op (inj▹ₗ-fork≡ ⦃ p ⦄ op) b)
--   inj▹ₗ-prong≡ ⦃ insert ⦄ op  = refl
--   inj▹ₗ-prong≡ ⦃ p = sift p ⦄ {op} b = inj▹ₗ-prong≡ ⦃ p ⦄ b
-- 
--   -- inj▹ᵣ-prong≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ {op : Op H′} (b : Fork H (inj▹ᵣ op))
--   --               → Prong H b ≡ Prong H′ (subst id (inj▹ᵣ-fork≡ ⦃ p ⦄ op) b)
--   -- inj▹ᵣ-prong≡ ⦃ insert ⦄ op  = refl
--   -- inj▹ᵣ-prong≡ ⦃ p = sift p ⦄ {inj₁ x} b = refl
--   -- inj▹ᵣ-prong≡ ⦃ p = sift p ⦄ {inj₂ y} b = inj▹ᵣ-prong≡ ⦃ p ⦄ b
-- 
-- 
--   proj-ret▹ₗ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Opᴴ H₀} → Retᴴ H (inj▹ₗ op) → Retᴴ H₀ op
--   proj-ret▹ₗ ⦃ w = insert ⦄ = id
--   proj-ret▹ₗ ⦃ w = sift w ⦄ = proj-ret▹ₗ ⦃ w ⦄
--   
--   proj-ret▹ᵣ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Opᴴ H′} → Retᴴ H (inj▹ᵣ op) → Retᴴ H′ op
--   proj-ret▹ᵣ ⦃ w = insert ⦄ = id
--   proj-ret▹ᵣ ⦃ w = sift w ⦄ {op = inj₁ x} = id
--   proj-ret▹ᵣ ⦃ w = sift w ⦄ {op = inj₂ y} = proj-ret▹ᵣ ⦃ w ⦄
-- 
--   proj-fork▹ₗ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Opᴴ H₀}
--                 → ((b : Op (Fork H₀ op)) → Hefty H (Ret (Fork H₀ op) b))
--                 → ((b : Op (Fork H (inj▹ₗ op))) → Hefty H (Ret (Fork H (inj▹ₗ op)) b))
--   proj-fork▹ₗ ⦃ w ⦄ {op} f b  =
--     let x = f (subst Op (inj▹ₗ-fork≡ ⦃ w ⦄ op) b) in
--     subst (Hefty _) (sym $ inj▹ₗ-prong≡ ⦃ w ⦄ b) x
\end{code}
%
\begin{code}
  ↑_ : ⦃ w : Lift Δ ≲ᴴ H ⦄ → (op : Op Δ) → Hefty H (Ret Δ op)
\end{code}
\begin{code}[hide]
  ↑_ op = impure (injᴴ {M = Hefty _} (op , pure , λ()))
\end{code}
%
Using this notion of lifting, \ad{Hefty} trees can be used to program against
interfaces of both higher-order and plain algebraic effects.


\subsection{Higher-Order Operations with Polymorphic Return Types}
\label{sec:hefty-monadic-bind}

Let us consider how to define \ad{Catch} as a higher-order effect.  Ideally, we
would define an operation that is parameterized by a return type of the branches
of a particular catch operation, as shown on the left, such that we can define
the higher-order effect signature on the right:\footnote{\textsf{\ab{d}} is for
  \textsf{\ab{dubious}}.}
%
\\
\begin{minipage}{0.495\linewidth}
\begin{code}
  data CatchOp̅ : Set₁ where
    catch̅ : Set → CatchOp̅
\end{code}
\begin{code}[hide]
  record Effectᴴ⅋ : Set₂ where
    field  Opᴴ     : Set₁
           Fork    : Opᴴ → Effect
           Retᴴ    : Opᴴ → Set
  open Effectᴴ⅋
\end{code}
\end{minipage}%
\hfill\vline\hfill
\begin{minipage}{0.495\linewidth}
\begin{code}
  Catch̅ : Effectᴴ⅋
  Opᴴ    Catch̅ = CatchOp̅
  Fork   Catch̅ (catch̅ A)  = record
    { Op = Bool; Ret = λ _ → A }
  Retᴴ   Catch̅ (catch̅ A)  = A
\end{code}
\end{minipage}%
\\
The \aF{Fork} field on the right says that \ad{Catch} has two sub-computations
(since \ad{Bool} has two constructors), and that each computation parameter has
some return type \ab{A}.  However, the signature on the right above is not well
defined!

The problem is that, because \ad{CatchOp̅} has a constructor that quantifies over
a type (\ad{Set}), the \ad{CatchOp̅} type lives in \ad{Set₁}.  Consequently it
does not fit the definition of \ad{Effectᴴ}, whose operations live in \ad{Set}.
There are two potential solutions to this problem: (1) increase the universe
level of \ad{Effectᴴ} to allow \aF{Opᴴ} to live in \ad{Set₁}; or (2) use a
\emph{universe of types}~\cite{martin-lof1984intuitionistic}.
%
Either solution is applicable here.  However, for some operations (e.g.,
$\lambda$ in \cref{sec:higher-order-lambda}) it is natural to model types as an
interface that we are programming against.  For this reason, using a type
universe is a natural fit.

A universe of types is a (dependent) pair of a syntax of types
(\aF{Ty}~\as{:}~\ad{Set}) and a semantic function
(\aF{⟦\_⟧ᵀ}~\as{:}~\aF{Ty}~\as{→}~\ad{Set}) defining the meaning of the syntax
by reflecting it into Agda's \ad{Set}:
%
\begin{code}
  record Universe : Set₁ where
    field  Type  : Set
           ⟦_⟧ᵀ  : Type → Set
\end{code}
\begin{code}[hide]
  open Universe ⦃ ... ⦄
\end{code}
%
Using type universes, we can parameterize the \ac{catch} constructor on the left
below by a \emph{syntactic type} \aF{Ty} of some universe \ab{u}, and use the
\emph{meaning of this type} (\aF{⟦}~\ab{t}~\aF{⟧ᵀ}) as the return type of the
computation parameters in the effect signature on the right below:
%
\begin{minipage}{0.495\linewidth}
\begin{code}
  data CatchOp ⦃ u : Universe ⦄ : Set where
    catch : Type → CatchOp
\end{code}
\end{minipage}
\hfill\vline\hfill
\begin{minipage}{0.495\linewidth}
\begin{code}
  Catch : ⦃ u : Universe ⦄ → Effectᴴ
  Opᴴ    Catch            = CatchOp
  Retᴴ   Catch (catch t)  = ⟦ t ⟧ᵀ
  Fork   Catch (catch t)  = Bool
  Ty     Catch {catch t}  = λ _ → ⟦ t ⟧ᵀ
\end{code}
\end{minipage}
\begin{code}[hide]
  ‵catch   : ⦃ u : Universe ⦄ ⦃ w : Catch ≲ᴴ H ⦄ {t : Type} 
           → Hefty H ⟦ t ⟧ᵀ → Hefty H ⟦ t ⟧ᵀ  → Hefty H ⟦ t ⟧ᵀ
\end{code}
\begin{code}[hide]
  ‵catch {t = t} m₁ m₂ = impure (injᴴ {M = Hefty _} {X = ⟦ t ⟧ᵀ} ((catch t) , pure , (if_then m₁ else m₂)))
\end{code}
%
While the universe of types encoding restricts the kind of type that catch can
have as a return type, the effect signature is parametric in the universe.  Thus
the implementer of the \ad{Catch} effect signature (or interface) is free to
choose a sufficiently expressive universe of types.

\subsection{Hefty Algebras}
\label{sec:hefty-algebras}

As shown in \cref{sec:higher-order-effects}, the higher-order catch operation
can be encoded as a non-modular elaboration:
%
\begin{code}[hide]
  catch⅋ : ⦃ Throw ≲ Δ ⦄ → Free Δ A → Free Δ A → Free Δ A
\end{code}
\begin{code}
  catch⅋ ⦃ w ⦄ m₁ m₂ = (♯ ((given hThrow handle m₁) tt)) 𝓑⅋ (maybe pure m₂)
\end{code}
\begin{code}[hide]
    where open FreeModule using () renaming (_𝓑_ to _𝓑⅋_)
          postulate instance foo : proj₁ w ≲ _ 
\end{code}
%
We can make this elaboration modular by expressing it as an \emph{algebra} over
\ad{Hefty} trees containing operations of the \ad{Catch} signature.  To this
end, we will use the following notion of hefty algebra (\ad{Algᴴ}) and fold (or
\emph{catamorphism}~\cite{DBLP:conf/fpca/MeijerFP91}, \af{cataᴴ}) for
\af{Hefty}:
%
\begin{code}
  record Algᴴ (H : Effectᴴ) (F : Set → Set) : Set₁ where
    field alg  : ⟦ H ⟧ᴴ F A → F A
\end{code}
%
\begin{code}[hide]
  open Algᴴ
\end{code}
\vspace{-1em}
\begin{code}
  cataᴴ : (∀ {A} → A → F A) → Algᴴ H F → Hefty H A → F A
  cataᴴ g a (pure x)               = g x
  cataᴴ g a (impure (op , k , s))  = alg a (op , ((cataᴴ g a ∘ k) , (cataᴴ g a ∘ s)))
\end{code}
%
Here \ad{Algᴴ} defines how to transform an \ac{impure} node of type
\ad{Hefty}~\ab{H}~\ab{A} into a value of type \ab{F}~\ab{A}, assuming we have
already folded the computation parameters and continuation into \ab{F} values.
A nice property of algebras is that they are closed under higher-order effect
signature sums:
%
\begin{code}[hide]
  infixr 12 _⋎_
\end{code}
\begin{code}
  _⋎_ : Algᴴ H₁ F → Algᴴ H₂ F → Algᴴ (H₁ ∔ H₂) F
  alg (A₁ ⋎ A₂) (inj₁ op , k , s) = alg A₁ (op , k , s)
  alg (A₁ ⋎ A₂) (inj₂ op , k , s) = alg A₂ (op , k , s)
\end{code}
%
By defining elaborations as hefty algebras (below) we can compose them using \ad{\_⋎\_}.
%
\begin{code}
  Elaboration : Effectᴴ → Effect → Set₁
  Elaboration H Δ = Algᴴ H (Free Δ)
\end{code}
%
An \af{Elaboration}~\ab{H}~\ab{Δ} elaborates higher-order operations of
signature \ab{H} into algebraic operations of signature \ab{Δ}.  Given an
elaboration, we can generically transform any hefty tree into more primitive
algebraic effects and handlers:
%
\begin{code}
  elaborate : Elaboration H Δ → Hefty H A → Free Δ A
  elaborate = cataᴴ pure
\end{code}

\paragraph{Exampl}
The elaboration below is analogous to the non-modular \af{catch} elaboration:
\begin{code}[hide]
module ElabModule where
  open FreeModule hiding (_𝓑_; _>>_)
  open HeftyModule hiding (_𝓑_; _>>_)
  open Algᴴ
  open Inverse ⦃ ... ⦄

  module _ where
    open FreeModule using (_𝓑_)

    eNil : Elaboration (Lift Nil) Δ
    alg eNil ()
\end{code}
\begin{code}
    eCatch : ⦃ u : Universe ⦄ ⦃ w : Throw ≲ Δ ⦄ →  Elaboration Catch Δ
    alg (eCatch ⦃ w = w ⦄) (catch t , k , s) = 
      (♯ ((given hThrow handle s true) tt)) 𝓑 maybe k (s false 𝓑 k)
\end{code}
\begin{code}[hide]
      where postulate instance foo : proj₁ w ≲ _ 
\end{code}
%
The elaboration is essentially the same as its non-modular counterpart, except
that it now uses the universe of types encoding discussed in
\cref{sec:hefty-monadic-bind}, and that it now transforms syntactic
representations of higher-order operations instead.
%
\begin{code}[hide]
  eLift : ⦃ Δ₁ ≲ Δ₂ ⦄ → Elaboration (Lift Δ₁) Δ₂
  alg (eLift ⦃ w ⦄) (op , k , s) = impure (inj (op , k))

  module Transact where
    open HeftyModule using (_𝓑_; _>>_)

    private
      data Type : Set where
        unit  : Type
        num   : Type

    private instance
      TypeUniverse : Universe
      Universe.Type TypeUniverse = Type
      Universe.⟦ TypeUniverse ⟧ᵀ unit  = ⊤
      Universe.⟦ TypeUniverse ⟧ᵀ num   = ℕ
\end{code}
%
Using this elaboration, we can, for example, run the following example program
involving the state effect from \cref{fig:state-effect-handler}, the throw
effect from \cref{sec:free-monad}, and the catch effect defined here:
%
\begin{code}
    transact  :  ⦃ wₛ  : Lift State ≲ᴴ H ⦄ ⦃ wₜ : Lift Throw ≲ᴴ H ⦄ ⦃ w : Catch ≲ᴴ H ⦄
              →  Hefty H ℕ
    transact = do
      ↑ put 1
      ‵catch (do ↑ (put 2); (↑ throw) 𝓑 ⊥-elim) (pure tt)
      ↑ get
\end{code}
%
The program first sets the state to 1; then to 2; and then throws an exception.
The exception is caught, and control is immediately passed to the final
operation in the program which gets the state.  By also defining elaborations
for \ad{Lift} and \ad{Nil}, we can elaborate and run the program:
%
\begin{code}
    eTransact : ⦃ Throw ≲ Δ ⦄ → ⦃ State ≲ Δ ⦄ → Elaboration (Catch ∔ Lift Throw ∔ Lift State ∔ Lift Nil) Δ
    eTransact = eCatch ⋎ eLift ⋎ eLift ⋎ eNil
\end{code}%
\vspace{-1em}%
\begin{code}
    -- test-transact : un (given hSt handle {!given hThrow handle ? $ tt!} $ 0) ≡ ((just 2 , 2))  un (  (  given hSt
    --                           handle (  (  given hThrow
    --                                        handle (elaborate eTransact transact)))
    --                                     tt ) 0 ) ≡ (just 2 , 2) -} 
    -- test-transact = refl
\end{code}
%
\noindent The program above uses a so-called \emph{global} interpretation of
state, where the \ac{put} operation in the ``try block'' of \ad{‵catch} causes
the state to be updated globally.  In \cref{sec:optional-transactional} we
return to this example and show how we can modularly change the elaboration of
the higher-order effect \ad{Catch} to yield a so-called \emph{transactional}
interpretation of state where the \ac{put} operation in the try block is rolled
back when an exception is thrown.


\subsection{Discussion and Limitations}
\label{sec:limitations}

Which (higher-order) effects can we describe using hefty trees and algebras?
Since the core mechanism of our approach is modular elaboration of higher-order
operations into more primitive effects and handlers, it is clear that hefty
trees and algebras are at least as expressive as standard algebraic effects.
The crucial benefit of hefty algebras over algebraic effects is that
higher-order operations can be declared and implemented modularly.  In this
sense, hefty algebras provide a modular abstraction layer over standard
algebraic effects that, although it adds an extra layer of indirection by
requiring both elaborations and handlers to give a semantics to hefty trees, is
comparatively cheap and implemented using only standard techniques such as
$F$-algebras.

Conceptually, we expect that hefty trees can capture any \emph{monadic}
higher-order effect whose signature is given by a higher-order functor on
$\ad{Set}~→~\ad{Set}$.  \citet{DBLP:conf/popl/Filinski99} showed that any
monadic effect can be represented using continuations, and given that we can
encode the continuation monad using algebraic effects~\cite{SchrijversPWJ19} in
terms of the \emph{sub/jump} operations (\cref{sec:optional-transactional}) by
\citet{thielecke1997phd,DBLP:conf/csl/FioreS14}, it is possible to elaborate any
monadic effect into algebraic effects using hefty algebras.  The current Agda
implementation, though, is slightly more restrictive.  The type of effect
signatures, \ad{Effectᴴ}, approximates the set of higher-order functors by
constructively enforcing that all occurrences of the computation type are
strictly positive.  Hence, there may be higher-order effects that are
well-defined semantically, but which cannot be captured in the Agda encoding
presented here.

When comparing hefty trees to scoped effects, we observe two important
differences.  The first difference is that the syntax of programs with
higher-order effects is fundamentally more restrictive when using scoped
effects.  Specifically, as discussed at the end of \cref{sec:scoped-discussion},
scoped effects impose a restriction on operations that their computation
parameters must pass control directly to the continuation of the operation.
Hefty trees, on the other hand, do not restrict the control flow of computation
parameters, meaning that they can be used to define a broader class of
operations.  For instance, in \cref{sec:higher-order-lambda} we define a
higher-order effect for function abstraction, which is an example of an
operation where control does not flow from the computation parameter to the
continuation.

The second difference is that hefty algebras and scoped effects and handlers are
modular in different ways.  Scoped effects are modular because we can modularly
define, compose, and handle scoped operations, by applying scoped effect
handlers in sequence; i.e.:
%
\begin{equation*}
\ad{Prog}~\ab{Δ₀~γ₀~A₀} \xrightarrow{h_1}
\ad{Prog}~\ab{Δ₁~γ₁~A₁} \xrightarrow{h_2}
\cdots
\xrightarrow{h_n}
\ad{Prog}~\ad{Nil}~\ad{Nil}~\ab{Aₙ}
\end{equation*}
%
As discussed in \cref{sec:weaving}, each handler application modularly
``weaves'' effects through sub computations, using a dedicated \aF{glue}
function.  Hefty algebras, on the other hand, work by applying an elaboration
algebra assembled from modular components in one go.  The program resulting from
elaboration can then be handled using standard algebraic effect handlers; i.e.:
%
\begin{equation*}
\ad{Hefty}~\as{(}\ab{H₀}~\ad{∔}~\cdots~\ad{∔}~\ab{Hₘ}\as{)}~\ab{A}
\xrightarrow{\af{elaborate}~\as{(}\ab{E₀}~\ad{⋎}~\cdots~\ad{⋎}~\ab{Eₘ}\as{)}}
\ad{Free}~Δ~A \xrightarrow{h_1}
\cdots \xrightarrow{h_k}
\ad{Free}~\ad{Nil}~\ab{Aₖ}
\end{equation*}
%
Because hefty algebras eagerly elaborate all higher-order effects in one go,
they do not require similar ``weaving'' as scoped effect handlers.  A
consequence of this difference is that scoped effect handlers exhibit more
effect interaction by default; i.e., different permutations of handlers may give
different semantics.  In contrast, when using hefty algebras we have to be more
explicit about such effect interactions.  We discuss this difference in more
detail in \cref{sec:optional-transactional}.

%%% Local Variables:
%%% reftex-default-bibliography: ("../references.bib")
%%% End:


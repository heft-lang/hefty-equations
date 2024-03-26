\begin{code}[hide]
{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}
module tex.sections.5-examples where

open import tex.sections.2-algebraic-effects
open import tex.sections.3-hefty-algebras

open import Function hiding (force; _↣_; _⟶_)
open import Data.Empty
open import Data.Unit
open import Data.Bool hiding (T)
open import Data.Sum
open import Data.Product
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.List using (List; []; _∷_; _++_; head)
open import Data.List.Membership.Propositional
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality hiding ([_])

\end{code}

\section{Examples}
\label{sec:examples}

As discussed in \cref{sec:higher-order-effects}, there is a wide range of examples of higher-order effects that cannot be defined as algebraic operations directly, and are typically defined as non-modular elaborations instead.
In this section we give examples of such effects and show to define them modularly using hefty algebras.
The artifact~\cite{heftyalgebraspopl23artifact} contains the full examples.


\subsection{$\lambda$ as a Higher-Order Operation}
\label{sec:higher-order-lambda}

\begin{code}[hide]
module AbstractionModule where
  open FreeModule hiding (_𝓑_; _>>_)
  open HeftyModule hiding (_𝓑_; _>>_)
  open Algᴴ
  open ⟨_!_⇒_⇒_!_⟩
  open Effect
  open Effectᴴ
  open Universe ⦃ ... ⦄
\end{code}

As recently observed by \citet{BergSPW21}, the (higher-order) operations for $\lambda$ abstraction and application are neither algebraic nor scoped effects.
We demonstrate how hefty algebras allow us to modularly define and elaborate an interface of higher-order operations for $\lambda$ abstraction and application, inspired by Levy's call-by-push-value \cite{Levy06}.
The interface we will consider is parametric in a universe of types given by the following record:

\begin{code}
  record LamUniverse : Set₁ where
    field  ⦃ u ⦄  : Universe
           _↣_    : Ty → Ty → Ty
           c      : Ty → Ty
\end{code}
%
The \aF{\_↣\_} field represents a function type, whereas \aF{c} is the type of \emph{thunk values}.
Distinguishing thunks in this way allows us to assign either a call-by-value or call-by-name semantics to the interface for $\lambda$ abstraction summarized by the following smart constructors:
%
\begin{code}[hide]
  open LamUniverse ⦃ ... ⦄

  module LamModule where
    open import Data.List.Relation.Unary.All
    open Inverse ⦃ ... ⦄

    -- Read : Set → Effect
    -- Op  (Read A)      = ReadOp
    -- Ret (Read A) ask  = A

    -- ‵ask : ⦃ Δ ∼ Read A ▸ Δ′ ⦄ → Free Δ A
    -- ‵ask ⦃ w ⦄ = impure (inj▸ₗ ask) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)


    -- hRead : ParameterizedHandler (Read A) A id
    -- ret hRead x _      = x
    -- hdl hRead ask k r  = k r r

    data LamOp ⦃ l : LamUniverse ⦄ : Set where
      lam : {t₁ t₂ : Ty}                     → LamOp
      var : {t : Ty}      → ⟦ c t ⟧ᵀ          → LamOp
      app : {t₁ t₂ : Ty}  → ⟦ (c t₁) ↣ t₂ ⟧ᵀ  → LamOp

    Lam : ⦃ l : LamUniverse ⦄ → Effectᴴ
    Opᴴ    Lam              = LamOp
    Fork  Lam (lam {t₁} {t₂})  =  record { Op = ⟦ c t₁ ⟧ᵀ; Ret = λ _ → ⟦ t₂ ⟧ᵀ }
    Retᴴ   Lam (lam {t₁} {t₂})  = ⟦ c t₁ ↣ t₂ ⟧ᵀ
    Fork  Lam (var x)  =  Nil
    Retᴴ   Lam (var {t} x)  = ⟦ t ⟧ᵀ
    Fork  Lam (app {t₁} {t₂} fun)  = record { Op = ⊤; Ret = λ _ → ⟦ t₁ ⟧ᵀ }
    Retᴴ   Lam (app {t₁} {t₂} fun)  = ⟦ t₂ ⟧ᵀ

    module _ ⦃ l : LamUniverse ⦄ ⦃ w : H ∼ Lam ▹ H′ ⦄ where
\end{code}
%
\begin{code}
      ‵lam  :  {t₁ t₂ : Ty}  → (⟦ c t₁ ⟧ᵀ → Hefty H ⟦ t₂ ⟧ᵀ)       → Hefty H ⟦ (c t₁) ↣ t₂ ⟧ᵀ
      ‵var  :  {t : Ty}      → ⟦ c t ⟧ᵀ                           → Hefty H ⟦ t ⟧ᵀ
      ‵app  :  {t₁ t₂ : Ty}  → ⟦ (c t₁) ↣ t₂ ⟧ᵀ → Hefty H ⟦ t₁ ⟧ᵀ  → Hefty H ⟦ t₂ ⟧ᵀ
\end{code}
\begin{code}[hide]
      ‵lam {t₁} {t₂} b = impure (inj▹ₗ (lam {t₁} {t₂})) (proj-fork▹ₗ b) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)
      ‵var x = impure (inj▹ₗ (var x)) (proj-fork▹ₗ (λ b → ⊥-elim b)) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)
      ‵app f m = impure (inj▹ₗ (app f)) (proj-fork▹ₗ (λ _ → m)) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)
\end{code}
%
Here \af{‵lam} is a higher-order operation with a function typed computation parameter and whose return type is a function value (\aF{⟦~c}~\ab{t₁}~\aF{↣}~\ab{t₂}~\aF{⟧ᵀ}).
The \af{‵var} operation accepts a thunk value as argument and yields a value of a matching type.
The \af{‵app} operation is also a higher-order operation: its first parameter is a function value type, whereas its second parameter is a computation parameter whose return type matches the function value parameter type.

The interface above defines a kind of \emph{higher-order abstract syntax}~\cite{PfenningE88} which piggy-backs on Agda functions for name binding.
However, unlike most Agda functions, the constructors above represent functions with side-effects.
The representation in principle supports functions with arbitrary side-effects since it is parametric in what  the higher-order effect signature \ab{H} is.
Furthermore, we can assign different operational interpretations to the operations in the interface without having to change the interface or programs written against the interface.
To illustrate we give two different implementations of the interface: one that implements a call-by-value evaluation strategy, and one that implements call-by-name.


\subsubsection{Call-by-Value}

We give a call-by-value interpretation \af{‵lam} by generically elaborating to algebraic effect trees with any set of effects \ab{Δ}.
Our interpretation is parametric in proof witnesses that the following isomorphisms hold for value types (\ad{↔} is the type of isomorphisms from the Agda standard library):\footnote{The two sides of an isomorphism \ab{A}~\ad{↔}~\ab{B} are given by the functions \aF{to}~\as{:}~\ab{A}~\as{→}~\ab{B} and \aF{from}~\as{:}~\ab{B}~\as{→}~\ab{A}.}
\begin{code}[hide]
    module _ ⦃ l : LamUniverse ⦄
             ⦃ iso₁ : {t₁ t₂ : Ty}
                    → ⟦ t₁ ↣ t₂ ⟧ᵀ ↔ (⟦ t₁ ⟧ᵀ → Free Δ ⟦ t₂ ⟧ᵀ) ⦄
             ⦃ iso₂ : {t : Ty}
                    → ⟦ c t ⟧ᵀ ↔ ⟦ t ⟧ᵀ  ⦄ where
      open FreeModule using (_𝓑_; _>>_) 
      open ElabModule
--      open Elab

      
      private _>>=_ = _𝓑_
      private postulate
\end{code}
\begin{code}
        iso₁⅋  : {t₁ t₂ : Ty}  → ⟦ t₁ ↣ t₂  ⟧ᵀ   ↔   (⟦ t₁ ⟧ᵀ → Free Δ ⟦ t₂ ⟧ᵀ)
        iso₂⅋  : {t : Ty}      → ⟦ c t      ⟧ᵀ   ↔   ⟦ t ⟧ᵀ
\end{code}
%
The first isomorphism says that a function value type corresponds to a function which accepts a value of type \ab{t₁} and produces a computation whose return type matches the function type.
The second says that thunk types coincide with value types.
Using these isomorphisms, the following defines a call-by-value elaboration of functions:
%
\begin{code}
      eLamCBV : Elaboration Lam Δ
      alg eLamCBV lam      ψ k = k (from ψ)
      alg eLamCBV (var x)  _ k = k (to x)
      alg eLamCBV (app f)  ψ k = do
        a ← ψ tt
        v ← to f (from a)
        k v
\end{code}
\begin{code}[hide]
      -- instance
      --   eLamCBV′ : Elab Lam Δ
      --   orate eLamCBV′ = eLamCBV
\end{code}
%
The \ac{lam} case passes the function body given by the sub-tree \ab{ψ} as a value to the continuation, where the \aF{from} function mediates the sub-tree of type \aF{⟦~c}~\ab{t₁}~\aF{⟧ᵀ}~\as{→}~\ad{Free}~\ab{Δ}~\aF{⟦}~\ab{t₂}~\aF{⟧ᵀ} to a value type \aF{⟦}~\as{(}\aF{c}~\ab{t₁}\as{)}~\aF{↣}~\ab{t₂}~\aF{⟧ᵀ}, using the isomorphism \af{iso₁}.
The \ac{var} case uses the \aF{to} function to mediate a \aF{⟦~c}~\ab{t}~\aF{⟧ᵀ} value to a \aF{⟦}~\ab{t}~\aF{⟧ᵀ} value, using the isomorphism \af{iso₂}.
The \ac{app} case first eagerly evaluates the argument expression of the application (in the sub-tree \ab{ψ}) to an argument value, and then passes the resulting value to the function value of the application.
The resulting value is passed to the continuation.

Using the elaboration above, we can evaluate programs such as the following which uses both the higher-order lambda effect, the algebraic state effect, and assumes that our universe has a number type \aF{⟦}~\ab{num}~\aF{⟧ᵀ}~\ad{↔}~\ad{ℕ}:
\begin{code}[hide]
    open import Data.Nat using (ℕ; _+_)
    module _ ⦃ u : LamUniverse ⦄ {num : Ty}
             ⦃ iso₁ : ⟦ num ⟧ᵀ ↔ ℕ ⦄ where
      open HeftyModule using (_𝓑_; _>>_)


      private _>>=_ = _𝓑_
\end{code}
\begin{code}
      ex : Hefty (Lam ∔ Lift State ∔ Lift Nil) ℕ
      ex = do
        ↑ put 1
        f ← ‵lam (λ x → do
              n₁ ← ‵var x
              n₂ ← ‵var x
              pure (from ((to n₁) + (to n₂))))
        v ← ‵app f incr
        pure (to v)
        where incr = do s₀ ← ↑ get; ↑ put (s₀ + 1); s₁ ← ↑ get; pure (from s₁)
\end{code}
The program first sets the state to \an{1}.
Then it constructs a function that binds a variable \ab{x}, dereferences the variable twice, and adds the two resulting values together.
Finally, the application in the second-to-last line applies the function with an argument expression which increments the state by \an{1} and returns the resulting value.
Running the program produces \an{4} since the state increment expression is eagerly evaluated before the function is applied.
%
\begin{code}[hide]
    module CBVExample where private
      open import Data.Nat using (ℕ)
      open HeftyModule using (_𝓑_; _>>_)
      open ElabModule
      open import Function.Construct.Identity    using (↔-id)
      open Inverse
      -- open Elab


      data Type : Set where
        _⟶_ : (t₁ t₂ : Type) → Type
        num : Type

      instance
        CBVUniverse : Universe
        Ty ⦃ CBVUniverse ⦄ = Type
        ⟦_⟧ᵀ ⦃ CBVUniverse ⦄ (t ⟶ t₁)  = ⟦ t ⟧ᵀ → Free (State ⊕ Nil) ⟦ t₁ ⟧ᵀ
        ⟦_⟧ᵀ ⦃ CBVUniverse ⦄ num       = ℕ

        iso-num : ℕ ↔ ⟦ num ⟧ᵀ
        iso-num = ↔-id _

        iso-fun : {t₁ t₂ : Type}
                → (⟦ t₁ ⟧ᵀ → Free (State ⊕ Nil) ⟦ t₂ ⟧ᵀ) ↔ ⟦ t₁ ⟶ t₂ ⟧ᵀ
        iso-fun = ↔-id _

        iso-c : {t : Type} → ⟦ t ⟧ᵀ ↔ ⟦ id t ⟧ᵀ
        iso-c = ↔-id _

        LamCBVUniverse : LamUniverse
        u    ⦃ LamCBVUniverse ⦄ = CBVUniverse
        _↣_  ⦃ LamCBVUniverse ⦄ = _⟶_
        c    ⦃ LamCBVUniverse ⦄ = id
\end{code}
\begin{code}
      elab-cbv : Elaboration (Lam ∔ Lift State ∔ Lift Nil) (State ⊕ Nil)
      elab-cbv = eLamCBV ⋎ eLift ⋎ eNil

      test-ex-cbv : un ((given hSt handle (elaborate elab-cbv ex)) 0) ≡ (4 , 2)
      test-ex-cbv = refl
\end{code}

\subsubsection{Call-by-Name}

The key difference between the call-by-value and the call-by-name interpretation of our $\lambda$ operations is that we now assume that thunks are computations.
That is, we assume that the following isomorphisms hold for value types:
\begin{code}[hide]
    module _ ⦃ u : LamUniverse ⦄
             ⦃ iso₁ : {t₁ t₂ : Ty}
                    → ⟦ t₁ ↣ t₂ ⟧ᵀ ↔ (⟦ t₁ ⟧ᵀ → Free Δ ⟦ t₂ ⟧ᵀ)  ⦄
             ⦃ iso₂ : {t : Ty}
                    → ⟦ c t ⟧ᵀ ↔ Free Δ ⟦ t ⟧ᵀ ⦄ where
      open FreeModule using (_𝓑_; _>>_) 
      open import Data.Nat using (ℕ)
      open ElabModule
--      open Elab

      private postulate
\end{code}
\begin{code}
        iso₁⅋  :  {t₁ t₂ : Ty}  → ⟦ t₁ ↣ t₂ ⟧ᵀ  ↔  (⟦ t₁ ⟧ᵀ → Free Δ ⟦ t₂ ⟧ᵀ)
        iso₂⅋  :  {t : Ty}      → ⟦ c t ⟧ᵀ      ↔  Free Δ ⟦ t ⟧ᵀ
\end{code}
Using these isomorphisms, the following defines a call-by-name elaboration of functions:
\begin{code}
      eLamCBN : Elaboration Lam Δ
      alg eLamCBN lam      ψ  k = k (from ψ)
      alg eLamCBN (var x)  _  k = to x 𝓑 k
      alg eLamCBN (app f)  ψ  k = to f (from (ψ tt)) 𝓑 k
\end{code}
\begin{code}[hide]
      -- instance
      --   eLamCBN′ : Elab Lam Δ
      --   orate eLamCBN′ = eLamCBN
\end{code}
%
The case for \ac{lam} is the same as the call-by-value elaboration.
The case for \ac{var} now needs to force the thunk by running the computation and passing its result to \ab{k}.
The case for \ac{app} passes the argument sub-tree (\ab{ψ}) as an argument to the function \ab{f}, runs the computation resulting from doing so, and then passes its result to \ab{k}.
%
\begin{code}[hide]
    module CBNExample where private
      open import Data.Nat using (ℕ)
      open HeftyModule using (_𝓑_; _>>_)
      open ElabModule
      open import Function.Construct.Identity    using (↔-id)
      open Inverse ⦃ ... ⦄
      -- open Elab


      data Type : Set where
        _⟶_ : (t₁ t₂ : Type)   → Type
        num  :                     Type
        susp : Type              → Type

      instance
        CBNUniverse : Universe
        Ty ⦃ CBNUniverse ⦄ = Type
        ⟦_⟧ᵀ ⦃ CBNUniverse ⦄ (t ⟶ t₁)  = ⟦ t ⟧ᵀ → Free (State ⊕ Nil) ⟦ t₁ ⟧ᵀ
        ⟦_⟧ᵀ ⦃ CBNUniverse ⦄ num        = ℕ
        ⟦_⟧ᵀ ⦃ CBNUniverse ⦄ (susp t)   = Free (State ⊕ Nil) ⟦ t ⟧ᵀ

        iso-num : ℕ ↔ ⟦ num ⟧ᵀ
        iso-num = ↔-id _

        iso-fun : {t₁ t₂ : Type}
                → (⟦ t₁ ⟧ᵀ → Free (State ⊕ Nil) ⟦ t₂ ⟧ᵀ) ↔ ⟦ t₁ ⟶ t₂ ⟧ᵀ
        iso-fun = ↔-id _

        iso-susp : {t : Ty}
                 → Free (State ⊕ Nil) ⟦ t ⟧ᵀ ↔ ⟦ susp t ⟧ᵀ
        iso-susp = ↔-id _

        LamCBNUniverse : LamUniverse
        u ⦃ LamCBNUniverse ⦄ = CBNUniverse
        _↣_ ⦃ LamCBNUniverse ⦄ = _⟶_
        c ⦃ LamCBNUniverse ⦄ = susp
\end{code}
%
Running the example program \af{ex} from above now produces \an{5} as result, since the state increment expression in the argument of \af{‵app} is thunked and run twice during the evaluation of the called function.
%
\begin{code}
      elab-cbn : Elaboration (Lam ∔ Lift State ∔ Lift Nil) (State ⊕ Nil)
      elab-cbn = eLamCBN ⋎ eLift ⋎ eNil

      test-ex-cbn : un ((given hSt handle (elaborate elab-cbn ex)) 0) ≡ (5 , 3)
      test-ex-cbn = refl
\end{code}


\subsection{Optionally Transactional Exception Catching}

A feature of scoped effect handlers~\cite{WuSH14,PirogSWJ18,YangPWBS22} is that changing the order of handlers makes it possible to obtain different semantics of \emph{effect interaction}.
A classical example of effect interaction is the interaction between state and exception catching that we briefly considered at the end of \cref{sec:hefty-algebras} in connection with this \ad{transact} program:
%
\begin{code}[hide]
  module CCModule where
    open import Data.Nat using (ℕ)
    open FreeModule hiding (_𝓑_; _>>_)
    open Abbreviation
    open ElabModule
    open Algᴴ
    open Inverse ⦃ ... ⦄

    ‵throwᴴ : ⦃ w : H  ∼  Lift Throw  ▹ H″ ⦄
             → Hefty H A
    ‵throwᴴ ⦃ w ⦄ = (↑ throw) 𝓑 ⊥-elim
      where open HeftyModule using (_𝓑_)

    module _ ⦃ u : Universe ⦄ {unit : Ty} ⦃ iso : ⟦ unit ⟧ᵀ ↔ ⊤ ⦄ where
      open HeftyModule using (_𝓑_; _>>_)
\end{code}    
\begin{code}
      transact⅋ : ⦃ wₛ : H ∼ Lift State ▹ H′ ⦄ ⦃ wₜ : H ∼  Lift Throw ▹ H″ ⦄ ⦃ w  : H ∼ Catch ▹ H‴ ⦄
                → Hefty H ℕ
      transact⅋ = do
        ↑ put 1
        ‵catch (do ↑ put 2; (↑ throw) 𝓑 ⊥-elim) (pure tt⅋)
        ↑ get
\end{code}
\begin{code}[hide]
        where tt⅋ = from tt
\end{code}
%
% The program first sets the state to \an{1}; then runs the ``try'' block of the \af{‵catch} operation, which sets the state to \an{2} and subsequently throws an exception.
% This causes the ``catch'' block of the \af{‵catch} operation to run, which does nothing.
% The last line of the program inspects the final state of the program.
% %
The state and exception catching effect can interact to give either of these two semantics:
\begin{enumerate}
\item \emph{Global} interpretation of state, where the \af{transact} program returns \an{2} since the \ac{put} operation in the ``try'' block causes the state to be updated globally.
\item \emph{Transactional} interpretation of state, where the \af{transact} program returns \an{1} since the state changes of the \ac{put} operation are \emph{rolled back} when the ``try'' block throws an exception.
\end{enumerate}
%
With monad transformers~\cite{cenciarelli1993syntactic,Liang1995monad} we can recover either of these semantics by permuting the order of monad transformers.
With scoped effect handlers we can also recover either by permuting the order of handlers.
However, the \ad{eCatch} elaboration in \cref{sec:hefty-algebras} always gives us a global interpretation of state.
In this section we demonstrate how we can recover a transactional interpretation of state by using a different elaboration of the \ac{catch} operation into an algebraically effectful program with the \ac{throw} operation and the off-the-shelf \emph{sub/jump} control effects due to \citet{thielecke1997phd,DBLP:conf/csl/FioreS14}.
The different elaboration is modular in the sense that we do not have to change the interface of the catch operation nor any programs written against the interface.

\subsubsection{Sub/Jump}
We recall how to define two operations, sub and jump, due to~\cite{thielecke1997phd,DBLP:conf/csl/FioreS14}.
We define these operations as algebraic effects following~\citet{SchrijversPWJ19}.
The algebraic effects are summarized by the following smart constructors where \ad{CC}~\ab{Ref} is associated with the sub/jump operations:
%
\begin{code}[hide]
    data CCOp ⦃ u : Universe ⦄ (Ref : Ty → Set) : Set where
      sub   : {t : Ty}                           →  CCOp Ref
      jump  : {t : Ty} (ref : Ref t) (x : ⟦ t ⟧ᵀ) →  CCOp Ref

    CC : ⦃ u : Universe ⦄ (Ref : Ty → Set) → Effect
    Op  (CC Ref) = CCOp Ref
    Ret (CC Ref) (sub {t})         = Ref t ⊎ ⟦ t ⟧ᵀ
    Ret (CC Ref) (jump ref x)  = ⊥

    module _ ⦃ u : Universe ⦄ {Ref : Ty → Set} {t : Ty} ⦃ w : Δ ∼ CC Ref ▸ Δ′ ⦄ where
\end{code}
\begin{code}
      ‵sub   : ⦃ w : Δ ∼ CC Ref ▸ Δ′ ⦄ (b : Ref t → Free Δ A) (k : ⟦ t ⟧ᵀ → Free Δ A)  → Free Δ A
      ‵jump  : ⦃ w : Δ ∼ CC Ref ▸ Δ′ ⦄ (ref : Ref t) (x : ⟦ t ⟧ᵀ)                        → Free Δ B
\end{code}
\begin{code}[hide]
      ‵sub b k =
        impure (inj▸ₗ ⦃ w ⦄ sub , [ b , k ] ∘  proj-ret▸ₗ ⦃ w ⦄)
      ‵jump ref x = impure
        (inj▸ₗ (jump ref x) ,
        ⊥-elim ∘ proj-ret▸ₗ ⦃ w ⦄)
\end{code}
%
An operation \af{‵sub}~\ab{f}~\ab{g} gives a computation \ab{f} access to the continuation \ab{g} via a reference value \ab{Ref}~\ab{t} which represents a continuation expecting a value of type \aF{⟦}~\ab{t}~\aF{⟧ᵀ}.
The \af{‵jump} operation invokes such continuations.
The operations and their handler (abbreviated to \af{h}) satisfy the following laws:
\begin{align*}
  \af{h}~\as{(}\af{‵sub}~\as{(λ~\_~→}~\ab{p}\as{)}~\ab{k}\as{)}
  &~\ad{≡}~\af{h}~\ab{p}
  \\
  \af{h}~\as{(}\af{‵sub}~\as{(λ}~\ab{r}~\as{→}~\ab{m}~\af{𝓑}~\af{‵jump}~\ab{r}\as{)}~\ab{k}\as{)}
   &~\ad{≡}~\af{h}~\as{(}\ab{m}~\af{𝓑}~\ab{k}\as{)}
  \\
  \af{h}~\as{(}\af{‵sub}~\ab{p}~\as{(}\af{‵jump}~\ab{r′}\as{))}
  &~\ad{≡}~\af{h}~\as{(}\ab{p}~\ab{r′}\as{)}
  \\
  \af{h}~\as{(}\af{‵sub}~\ab{p}~\ab{q}~\af{𝓑}~\ab{k}\as{)}
 &~\ad{≡}~\af{h}~\as{(}\af{‵sub}~\as{(λ}~\ab{x}~\as{→}~\ab{p}~\ab{x}~\af{𝓑}~\ab{k}~\as{)}~\as{(λ}~\ab{x}~\as{→}~\ab{q}~\ab{x}~\af{𝓑}~\ab{k}\as{))}
\end{align*}
The last law asserts that \af{‵sub} and \af{‵jump} are \emph{algebraic} operations, since their computational sub-terms behave as continuations.
Thus, we encode \af{‵sub} and its handler as an algebraic effect.
%
\begin{code}[hide]
    module _ ⦃ u : Universe ⦄ where
\end{code}
\begin{code}[hide]
      hCC : ⟨ A ! (CC (λ t → ⟦ t ⟧ᵀ → Free Δ′ A)) ⇒ ⊤ ⇒ A ! Δ′ ⟩
      ret  hCC a _ = pure a
      hdl  hCC (sub     ,    k) p = let c = flip k p ∘ inj₂
        in k (inj₁ c) p
      hdl  hCC (jump ref x , k) _ = ref x
\end{code}
%
\begin{code}[hide]
    private
      open import Data.Nat using (ℕ) renaming (_+_ to _ℕ+_)
      open import Effect.Monad

      data Type : Set where
        num : Type

      instance
        NumUniverse : Universe
        Ty   ⦃ NumUniverse ⦄      = Type
        ⟦_⟧ᵀ  ⦃ NumUniverse ⦄ num  = ℕ

      Cont : Effect → Set → Type → Set
      Cont Δ A t = ⟦ t ⟧ᵀ → Free Δ A

      ex₀ : Free (CC (Cont Δ ℕ) ⊕ Δ) ℕ
      ex₀ = do
        ‵sub (λ ref → ‵jump ref 41) (λ x → pure (x ℕ+ 1))

      test₀ : un ((given hCC handle ex₀) tt) ≡ 42
      test₀ = refl

      ex₁ : Free (CC (Cont Δ ℕ) ⊕ Δ) ℕ
      ex₁ = do
        ‵sub (λ ref → pure 41) (λ x → pure (x ℕ+ 1))

      test₁ : un ((given hCC handle ex₁) tt) ≡ 41
      test₁ = refl
\end{code}


\subsubsection{Optionally Transactional Exception Catching}
\label{sec:optional-transactional}

By using the \af{‵sub} and \af{‵jump} operations in our elaboration of \ad{catch}, we get a semantics of exception catching whose interaction with state depends on the order that the state effect and sub/jump effect is handled.
%
\begin{code}[hide]
  module TransactionalCatch where
    open CCModule
    open Abbreviation

    module _ ⦃ u : Universe ⦄
             {Ref : Ty → Set}
             {unit : Ty}
             ⦃ iso : ⟦ unit ⟧ᵀ ↔ ⊤ ⦄
             where
      open FreeModule using (_𝓑_; _>>_)
      open ElabModule
--      open Elab
      open Inverse ⦃ ... ⦄
\end{code}
\begin{code}
      eCatchOT : ⦃ w₁ : Δ ∼ CC Ref ▸ Δ′ ⦄ ⦃ w₂ : Δ ∼ Throw ▸ Δ″ ⦄ → Elaboration Catch Δ
      alg eCatchOT (catch x) ψ k = let m₁ = ψ true; m₂ = ψ false in
        ‵sub  (λ r → (♯ ((given hThrow handle m₁) tt)) 𝓑 maybe k (‵jump r (from tt)))
              (λ _ → m₂ 𝓑 k)
\end{code}
%
The elaboration uses \af{‵sub} to capture the continuation of a higher-order \ac{catch} operation.
If no exception is raised, then control flows to the continuation \ab{k} without invoking the continuation of \af{‵sub}.
Otherwise, we jump to the continuation of \af{‵sub}, which runs \ab{m₂} before passing control to \ab{k}.
Capturing the continuation in this way interacts with state because the continuation of \af{‵sub} may have been pre-applied to a state handler that only knows about the ``old'' state.
This happens when we invoke the state handler before the handler for sub/jump: in this case we get the transactional interpretation of state, so running \af{transact} gives \an{1}.
Otherwise, if we run the sub/jump handler before the state handler, we get the global interpretation of state and the result \an{2}.
%
\begin{code}[hide]
      -- instance
      --   eCatchOT′ : Elab Catch Δ
      --   orate eCatchOT′ = eCatchOT

    module _ where
      open HeftyModule using (_𝓑_; _>>_)
      open import Data.Nat using (ℕ; _+_)
      open Inverse ⦃ ... ⦄
    
      transact : ⦃ u : Universe ⦄
               → ⦃ wₛ  : H  ∼  Lift State  ▹ H′ ⦄
               → ⦃ wₜ  : H  ∼  Lift Throw  ▹ H″ ⦄
               → ⦃ w   : H  ∼  Catch       ▹ H‴ ⦄
               → {unit : Ty} ⦃ iso : ⊤ ↔ ⟦ unit ⟧ᵀ ⦄
               → Hefty H ℕ
      transact {unit = unit} = do
        ↑ (put 1)
        ‵catch (do ↑ (put 2); ((↑ throw) 𝓑 ⊥-elim)) (pure (to tt))
        ↑ get

    module CatchExample where private
      open import Data.Nat using (ℕ)
      open ElabModule
      open Inverse ⦃ ... ⦄
      open import Function.Construct.Identity    using (↔-id)
      -- open Elab

      data Type : Set where
        unit   : Type
        num : Type

      instance
        CatchUniverse : Universe
        Ty   ⦃ CatchUniverse ⦄ = Type
        ⟦_⟧ᵀ ⦃ CatchUniverse ⦄ unit   = ⊤
        ⟦_⟧ᵀ ⦃ CatchUniverse ⦄ num = ℕ

        iso-1 : ⊤ ↔ ⟦ unit ⟧ᵀ
        iso-1 = ↔-id _

      transact-elab₂ : Elaboration
                         (Lift State ∔ Lift Throw ∔ Catch ∔ Lift Nil)
                         (CC (λ t → ⟦ t ⟧ᵀ → Free Nil A) ⊕ State ⊕ Throw ⊕ Nil)
      transact-elab₂ = eLift ⋎ eLift ⋎ eCatchOT ⋎ eNil

      transact-elab₃ : Elaboration
                         (Lift State ∔ Lift Throw ∔ Catch ∔ Lift Nil)
                         (CC (λ t → ⟦ t ⟧ᵀ → Free (State ⊕ Nil) A) ⊕ State ⊕ Throw ⊕ Nil)
      transact-elab₃ = eLift ⋎ eLift ⋎ eCatchOT ⋎ eNil
\end{code}
\begin{code}[hide]
      test-transact₂ :  un
                          (given hCC
                           handle (given hThrow
                                   handle (given hSt
                                           handle (elaborate transact-elab₂ transact) $ 0)
                                  $ tt)
                           $ tt)
                          ≡ just (1 , 1)
      test-transact₂ = refl

      test-transact₃ : un (given hSt
                           handle (given hCC
                                   handle (given hThrow
                                           handle (elaborate transact-elab₃ transact)
                                          $ tt)
                                  $ tt)
                          $ 0) ≡ (just 2 , 2)
      test-transact₃ = refl
\end{code}
\begin{code}[hide]
      transact′ : ⦃ wₛ : H ∼ Lift State ▹ H′ ⦄ ⦃ wₜ : H ∼  Lift Throw ▹ H″ ⦄ ⦃ w  : H ∼ Catch ▹ H‴ ⦄
                → Hefty H ℕ
      transact′ = do
        ↑ put 1
        ‵catch (do ↑ put 2) (pure (from tt))
        ↑ get
        where open HeftyModule using (_>>_)

      test-transact₂′ : un (given hCC
                            handle (given hThrow
                                    handle (given hSt
                                            handle (elaborate transact-elab₂ transact′) $ 0)
                                   $ tt)
                           $ tt) ≡ just (2 , 2)
      test-transact₂′ = refl

      test-transact₃′ : un (given hSt
                           handle (given hCC
                                   handle (given hThrow
                                           handle (elaborate transact-elab₃ transact′)
                                          $ tt)
                                  $ tt)
                          $ 0) ≡ (just 2 , 2)
      test-transact₃′ = refl


      transact″ : ⦃ wₛ : H ∼ Lift State ▹ H′ ⦄ ⦃ wₜ : H ∼  Lift Throw ▹ H″ ⦄ ⦃ w  : H ∼ Catch ▹ H‴ ⦄
                → Hefty H ℕ
      transact″ = do
        ↑ put 1
        ‵catch (do ↑ put 2; ‵throwᴴ) (↑ get)
        where open HeftyModule using (_>>_)
        
      test-transact₂″ : un (given hCC
                            handle (given hThrow
                                    handle (given hSt
                                            handle (elaborate transact-elab₂ transact″) $ 0)
                                   $ tt)
                           $ tt) ≡ just (1 , 1)
      test-transact₂″ = refl

      test-transact₃″ : un (given hSt
                           handle (given hCC
                                   handle (given hThrow
                                           handle (elaborate transact-elab₃ transact″)
                                          $ tt)
                                  $ tt)
                          $ 0) ≡ (just 2 , 2)
      test-transact₃″ = refl
\end{code}

The sub/jump elaboration above is more involved than the scoped effect handler that we considered in \cref{sec:scoped-effects}.
However, the complicated encoding does not pollute the higher-order effect interface, and only turns up if we strictly want or need effect interaction.


\subsection{Logic Programming}

Following \cite{DBLP:conf/ppdp/SchrijversWDD14,WuSH14,YangPWBS22} we can define a non-deterministic choice operation (\af{\_‵or\_}) as an algebraic effect, to provide support for expressing the kind of non-deterministic search for solutions that is common in logic programming.
We can also define a \af{‵fail} operation which indicates that the search in the current branch was unsuccessful.
The smart constructors below are the lifted higher-order counterparts to the \af{‵or} and \af{‵fail} operations:
\begin{code}[hide]
  module ChoiceModule where
    open Abbreviation
    open Algᴴ
    open ElabModule
--    open Elab
\end{code}
\begin{code}[hide]
    data ChoiceOp : Set where
      or    : ChoiceOp
      fail  : ChoiceOp

    Choice : Effect
    Op  Choice = ChoiceOp
    Ret Choice or = Bool
    Ret Choice fail = ⊥
\end{code}
\begin{code}[hide]
    ‵fail : ⦃ Δ ∼ Choice ▸ Δ′ ⦄ → Free Δ A
    -- _‵or_ : ⦃ Δ ∼ Choice ▸ Δ′ ⦄ → Free Δ A → Free Δ A → Free Δ A
\end{code}
\begin{code}[hide]
    -- _‵or_ ⦃ w ⦄ m₁ m₂ = impure (inj▸ₗ or) ((if_then m₁ else m₂) ∘ proj-ret▸ₗ ⦃ w ⦄)
    ‵fail ⦃ w ⦄ = impure (inj▸ₗ fail , ⊥-elim ∘ proj-ret▸ₗ ⦃ w ⦄)
\end{code}
\begin{code}[hide]
    module _ where
      open FreeModule using (_𝓑_; _>>_)
      open ElabModule

      private _>>=_ = _𝓑_

      hChoice : ⟨ A ! Choice ⇒ ⊤ ⇒ List A ! Δ ⟩
      ret hChoice a _ = pure (a ∷ [])
      hdl hChoice (or , k) p = do
        l₁ ← k true   p
        l₂ ← k false  p
        pure (l₁ ++ l₂)
      hdl hChoice (fail , k) _ = pure []
\end{code}
\begin{code}[hide]
      data OnceOp ⦃ u : Universe ⦄ : Set where once : {t : Ty} → OnceOp

      Once : ⦃ u : Universe ⦄ → Effectᴴ
      Opᴴ    Once          = OnceOp
      Fork   Once (once {t}) = record
        { Op = ⊤; Ret = λ _ →  ⟦ t ⟧ᵀ }
      Retᴴ   Once (once {t}) = ⟦ t ⟧ᵀ
\end{code}
\begin{code}
      _‵orᴴ_  : ⦃ H ∼ Lift Choice ▹ H′ ⦄ → Hefty H A → Hefty H A  → Hefty H A
      ‵failᴴ  : ⦃ H ∼ Lift Choice ▹ H′ ⦄                          → Hefty H A
\end{code}
\begin{code}[hide]
      _‵orᴴ_ ⦃ w ⦄ m₁ m₂ = (↑ or) 𝓑' (if_then m₁ else m₂)
        where open HeftyModule renaming (_𝓑_ to _𝓑'_)

      ‵failᴴ ⦃ w ⦄ = (↑ fail) 𝓑' ⊥-elim
        where open HeftyModule renaming (_𝓑_ to _𝓑'_)

      module _ ⦃ u : Universe ⦄ where
\end{code}
A useful operator for cutting non-deterministic search short when a solution is found is the \af{‵once} operator.
The \af{‵once} operator is not an algebraic effect, but a scoped (and thus higher-order) effect.
\begin{code}
        ‵once : ⦃ w : H ∼ Once ▹ H′ ⦄ {t : Ty} → Hefty H ⟦ t ⟧ᵀ → Hefty H ⟦ t ⟧ᵀ
\end{code}
\begin{code}[hide]
        ‵once ⦃ w ⦄ {t} b = impure (inj▹ₗ once) (proj-fork▹ₗ (λ _ → b)) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)

      module _ ⦃ u : Universe ⦄ where
\end{code}
We can define the meaning of the \af{once} operator as the following elaboration:
\begin{code}
        eOnce : ⦃ Δ ∼ Choice ▸ Δ′ ⦄ → Elaboration Once Δ
        alg eOnce once ψ k = do
          l ← ♯ ((given hChoice handle (ψ tt)) tt)
          maybe k ‵fail (head l)
\end{code}
The elaboration runs the branch (\ab{ψ}) of \ac{once} under the \af{hChoice} handler to compute a list of all solutions of \ab{ψ}.
It then tries to choose the first solution and pass that to the continuation \ab{k}.
If the branch has no solutions, we fail.
%
Under a strict evaluation order, the elaboration computes all possible solutions which is doing more work than needed.
Agda 2.6.2.2 does not have a specified evaluation strategy, but does compile to Haskell which is lazy.
In Haskell, the solutions would be lazily computed, such that the \ac{once} operator cuts search short as intended.

\begin{code}[hide]
        -- instance
        --   eOnce′ : ⦃ w : Δ ∼ Choice ▸ Δ′ ⦄ → Elab Once Δ
        --   orate eOnce′ = eOnce
\end{code}

\begin{code}[hide]
    module OnceExample where
      open import Data.Nat using (ℕ; _≡ᵇ_)
      open HeftyModule using (_𝓑_; _>>_)
      open ElabModule

      private _>>=_ = _𝓑_

      data Type : Set where
        num   : Type
        unit  : Type

      private instance
        OnceUniverse : Universe
        Ty ⦃ OnceUniverse ⦄ = Type
        ⟦_⟧ᵀ ⦃ OnceUniverse ⦄ num = ℕ
        ⟦_⟧ᵀ ⦃ OnceUniverse ⦄ unit = ⊤

      ex-0or1 : Hefty (Lift Choice ∔ Once ∔ Lift Nil) ℕ
      ex-0or1 = (pure 0) ‵orᴴ (pure 1)

      ex-fail-once : Hefty (Lift Choice ∔ Once ∔ Lift Nil) ℕ
      ex-fail-once = do
        r ← ‵once ex-0or1
        if r ≡ᵇ 0 then ‵failᴴ else pure r
                                        
      once-elab : Elaboration (Lift Choice ∔ Once ∔ Lift Nil) (Choice ⊕ Nil)
      once-elab = eLift ⋎ eOnce ⋎ eNil

      test-ex-0or1 : un (given hChoice handle (elaborate once-elab ex-0or1) $ tt) ≡ 0 ∷ 1 ∷ []
      test-ex-0or1 = refl

      test-fail-once : un (given hChoice handle (elaborate once-elab ex-fail-once) $ tt) ≡ []
      test-fail-once = refl
\end{code}


\subsection{Concurrency}

Finally, we consider how to define higher-order operations for concurrency, inspired by \citeauthor{YangPWBS22}'s~[\citeyear{YangPWBS22}] \emph{resumption monad}~\cite{Claessen99,Schmidt1986denotational,PirogG14} definition using scoped effects.
We summarize our encoding and compare it with the resumption monad. The goal is to define the following operations:
%
%Our goal is to define two higher-order operations:
%
\begin{code}[hide]
  module _ ⦃ u : Universe ⦄ where
    postulate
\end{code}
\begin{code}
      ‵spawn⅋   : {t : Ty} → (m₁ m₂ : Hefty H ⟦ t ⟧ᵀ)  → Hefty H ⟦ t ⟧ᵀ
      ‵atomic⅋  : {t : Ty} → Hefty H ⟦ t ⟧ᵀ            → Hefty H ⟦ t ⟧ᵀ
\end{code}
%
The operation \af{‵spawn}~\ab{m₁}~\ab{m₂} spawns two threads that run concurrently, and returns the value produced by \ab{m₁} after both have finished.
The operation \af{‵atomic}~\ab{m} represents a block to be executed atomically; i.e., no other threads run before the block finishes executing.

We elaborate \ad{‵spawn} by interleaving the sub-trees of its computations.
To this end, we use a dedicated function which interleaves the operations in two trees and yields as output the value of the left input tree (the first computation parameter):
%
\begin{code}[hide]
  module _ ⦃ u : Universe ⦄ where
    open CCModule
    postulate
\end{code}
\begin{code}
      interleaveₗ⅋  :  {Ref : Ty → Set} → Free (CC Ref ⊕ Δ) A → Free (CC Ref ⊕ Δ) B
                    →  Free (CC Ref ⊕ Δ) A  
\end{code}
%
\begin{code}[hide]
  module ResumptionModule where

    module _ where
      open FreeModule
      open ElabModule
      open CCModule
--      open Elab


      -- interleaving interleaves two trees, except for sub-scopes of atomic blocks

      interleaveₗ : ⦃ u : Universe ⦄ {Ref : Ty → Set} {-⦃ w : Δ ∼ Choice ▸ Δ′ ⦄-}
                  → Free (CC Ref ⊕ Δ) A → Free (CC Ref ⊕ Δ) B → Free (CC Ref ⊕ Δ) A
      interleaveₗ (pure x) (pure _) = pure x
      interleaveₗ (pure x) m₂ = fmap (λ _ → x) m₂
      interleaveₗ m₁ (pure x) = m₁
      interleaveₗ (impure (inj₁ (jump ref x) , _)) m₂ = do
        m₂
        ‵jump ref x
      interleaveₗ m₁ (impure (inj₁ (jump ref x) , _)) = do
        m₁
        ‵jump ref x
      interleaveₗ (impure (inj₁ sub , k₁)) (impure (inj₁ sub , k₂)) =
        impure
          (inj₁ sub , 
          (λ{ (inj₁ x) → k₁ (inj₁ x)
            ; (inj₂ y) →
              impure
                (inj₁ sub , 
                (λ{ (inj₁ x) → k₂ (inj₁ x) 𝓑 λ _ → k₁ (inj₂ y)
                  ; (inj₂ z) → interleaveₗ (k₁ (inj₂ y)) (k₂ (inj₂ z)) })) }))
      interleaveₗ (impure (inj₁ sub , k₁)) (impure (inj₂ op₂ , k₂)) = do
        impure
          (inj₁ sub ,
          (λ{ (inj₁ x) → k₁ (inj₁ x)
            ; (inj₂ y) →
              impure
                (inj₂ op₂ , 
                (λ z → interleaveₗ (k₁ (inj₂ y)) (k₂ z))) }))
      interleaveₗ (impure (inj₂ op₁ , k₁)) (impure (inj₁ sub , k₂)) =
        impure
          (inj₂ op₁ , 
          (λ x →
            impure
              (inj₁ sub , 
              (λ{ (inj₁ y) → k₂ (inj₁ y) 𝓑 λ _ → k₁ x
                ; (inj₂ z) → interleaveₗ (k₁ x) (k₂ (inj₂ z)) }))))
      interleaveₗ (impure (inj₂ op₁ , k₁)) (impure (inj₂ op₂ , k₂)) =
        impure (inj₂ op₁ , λ x₁ → impure (inj₂ op₂ , λ x₂ → interleaveₗ (k₁ x₁) (k₂ x₂)))


      -- higher-order operation for concurrency that desugars into interleaving and atomic

      data ConcurOp ⦃ u : Universe ⦄ : Set where
        spawn   : (t : Ty) → ConcurOp
        atomic  : (t : Ty) → ConcurOp

      Concur : ⦃ u : Universe ⦄ → Effectᴴ
      Opᴴ Concur    = ConcurOp
      
      Fork Concur (spawn t) = record
        { Op = Bool; Ret = λ _ → ⟦ t ⟧ᵀ }
      Retᴴ Concur (spawn t) = ⟦ t ⟧ᵀ

      Fork Concur (atomic t)   = record
        { Op = ⊤; Ret = λ _ → ⟦ t ⟧ᵀ }
      Retᴴ Concur (atomic t)    = ⟦ t ⟧ᵀ


      module _ ⦃ u : Universe ⦄ where
        ‵spawn : ⦃ w : H ∼ Concur ▹ H′ ⦄ {t : Ty}
               → Hefty H ⟦ t ⟧ᵀ → Hefty H ⟦ t ⟧ᵀ → Hefty H ⟦ t ⟧ᵀ
        ‵spawn ⦃ w = w ⦄ {t} m₁ m₂ =
          impure (inj▹ₗ (spawn t)) (proj-fork▹ₗ (λ b → if b then m₁ else m₂)) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)

        ‵atomic : ⦃ w : H ∼ Concur ▹ H′ ⦄ {t : Ty}
                 → Hefty H ⟦ t ⟧ᵀ → Hefty H ⟦ t ⟧ᵀ
        ‵atomic ⦃ w = w ⦄ {t} m = impure (inj▹ₗ (atomic t)) (proj-fork▹ₗ (λ _ → m)) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)
\end{code}
%
%
Here, the \ad{CC} effect is the sub/jump effect that we also used in \cref{sec:optional-transactional}.
The \af{interleaveₗ} function ensures atomic execution by only interleaving code that is not wrapped in a \af{‵sub} operation.
We elaborate \ad{Concur} into \ad{CC} as follows, where the \af{to-front} and \af{from-front} functions use the row insertion witness \ab{wₐ} to move the \ad{CC} effect to the front of the row and back again:
%
\begin{code}
        eConcur : {Ref : Ty → Set} ⦃ w : Δ ∼ CC Ref ▸ Δ″ ⦄ → Elaboration Concur Δ
        alg eConcur (spawn t)   ψ k  =
          from-front (interleaveₗ (to-front (ψ true)) (to-front (ψ false))) 𝓑 k
        alg eConcur (atomic t)  ψ k  = ‵sub (λ ref → ψ tt 𝓑 ‵jump ref) k
\end{code}
%
The elaboration uses \af{‵sub} as a delimiter for blocks that should not be interleaved, such that the \af{interleaveₗ} function only interleaves code that does not reside in atomic blocks.
At the end of an \ac{atomic} block, we \af{‵jump} to the (possibly interleaved) computation context, \ab{k}.
By using \af{‵sub} to explicitly delimit blocks that should not be interleaved, we have encoded what \citet[\S{}~7]{WuSH14} call \emph{scoped syntax}.

\paragraph*{Example}
  Below is an example program that spawns two threads that use the \ad{Output} effect.
  The first thread prints \an{0}, \an{1}, and \an{2}; the second prints \an{3} and \an{4}.
%
\begin{code}[hide]
    module ConcurExample where
      open import Data.Nat using (ℕ)
      -- open OutModule
      open HeftyModule
      open FreeModule hiding (_𝓑_; _>>_)
      open ElabModule
      open CCModule
      -- open Elab

      data Type : Set where
        unit : Type
        num : Type

      instance
        ConcurUniverse : Universe
        Ty ⦃ ConcurUniverse ⦄ = Type
        ⟦_⟧ᵀ ⦃ ConcurUniverse ⦄ unit = ⊤
        ⟦_⟧ᵀ ⦃ ConcurUniverse ⦄ num = ℕ
\end{code}
\begin{code}
      ex-01234 : Hefty (Lift Output ∔ Concur ∔ Lift Nil) ℕ
      ex-01234 = ‵spawn  (do ↑ out "0"; ↑ out "1"; ↑ out "2"; pure 0)
                         (do ↑ out "3"; ↑ out "4"; pure 0)
\end{code}
%
Since the \ad{Concur} effect is elaborated to interleave the effects of the two threads, the printed output appears in interleaved order:
%
\begin{code}[hide]
      concur-elab : Elaboration
                         (Lift Output ∔ Concur ∔ Lift Nil)
                         (  CC (λ t → ⟦ t ⟧ᵀ → Free (Output ⊕ Nil) ℕ)
                         ⊕ Output
                         ⊕ Nil )
      concur-elab = eLift ⋎ eConcur ⋎ eNil
\end{code}
\begin{code}
      test-ex-01234 :  un (  (  given hOut
                                handle (  (  given hCC
                                             handle (elaborate concur-elab ex-01234)
                                          ) tt ) ) tt ) ≡ (0 , "03142")
      test-ex-01234 = refl
\end{code}
%
The following program spawns an additional thread with an \ad{‵atomic} block
%
\begin{code}
      ex-01234567 : Hefty (Lift Output ∔ Concur ∔ Lift Nil) ℕ
      ex-01234567 = ‵spawn  ex-01234
                            (‵atomic (do ↑ out "5"; ↑ out "6"; ↑ out "7"; pure 0))
\end{code}
%
Inspecting the output, we see that the additional thread indeed computes atomically:
%
\begin{code}
      test-ex-01234567 :  un (  (  given hOut
                                   handle (  (  given hCC
                                                handle (elaborate concur-elab ex-01234567)
                                             ) tt ) ) tt ) ≡ (0 , "05673142")
      test-ex-01234567 = refl
\end{code}
%
\begin{code}[hide]
      concur-elab′ : Elaboration
                         (Lift Output ∔ Concur ∔ Lift Nil)
                         (  Output
                         ⊕ CC (λ t → ⟦ t ⟧ᵀ → Free Nil (ℕ × String))
                         ⊕ Nil )
      concur-elab′ = eLift ⋎ eConcur ⋎ eNil

      test-ex′ : un (  (  given hCC
                          handle (  (  given hOut
                                       handle (elaborate concur-elab′ ex-01234) )
                                    tt ) ) tt ) ≡ (0 , "03142")
      test-ex′ = refl

      ex-atomic-01234 : Hefty (Lift Output ∔ Concur ∔ Lift Nil) ℕ
      ex-atomic-01234 = ‵spawn (‵atomic (do ↑ out "0"; ↑ out "1"; ↑ out "2"; pure 0)) (do ↑ out "3"; ↑ out "4"; pure 0)

      -- ordering of handlers matters!
      test-atomic-ex : un ((given hCC handle ((given hOut handle (elaborate concur-elab′ ex-atomic-01234)) tt)) tt) ≡ (0 , "34")
      test-atomic-ex = refl
\end{code}

The example above is inspired by the resumption monad, and in particular by the scoped effects definition of concurrency due to \citet{YangPWBS22}.
\citeauthor{YangPWBS22} do not (explicitly) consider how to define the concurrency operations in a modular style.
Instead, they give a direct semantics that translates to the resumption monad which we can encode as follows in Agda (assuming resumptions are given by the free monad):
%
\begin{code}
  data Resumption Δ A : Set where
    done  : A                        → Resumption Δ A
    more  : Free Δ (Resumption Δ A)  → Resumption Δ A
\end{code}
%
We could elaborate into this type using a hefty algebra \ad{Algᴴ}~\ad{Concur}~\as{(}\ad{Resumption}~\ab{Δ}\as{)} but that would be incompatible with our other elaborations which use the free monad.
For that reason, we emulate the resumption monad using the free monad instead of using the \ad{Resumption} type directly.


%%% Local Variables:
%%% reftex-default-bibliography: ("../references.bib")
%%% End:

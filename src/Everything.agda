{-# OPTIONS --without-K #-} 

module Everything where

-- Some categorical structors (mostly related to functors) 
open import Core.Functor
open import Core.Functor.NaturalTransformation
open import Core.Functor.HigherOrder
open import Core.Functor.Monad

-- Strictly-postive-by-construction encodings of (higher-order) functors 
open import Core.Container
open import Core.Signature

-- Defines ternary separation, and monotone predicates based on their respective
-- extension order
open import Core.Ternary
open import Core.MonotonePredicate

-- Needed for proofs about containers, as they use function spaces to encode
-- branching
open import Core.Extensionality

-- The syntax of effectful programs, defined as the free monad over a
-- (higher-order) signature
open import Effect.Syntax.Free
open import Effect.Syntax.Hefty

-- Ternary separation for effects. The induced extension order and corresponding
-- modal separation logic is useful for characterizing operations over effectful
-- programs and friends, such as equations, theories, and elaborations.
open import Effect.Separation
open import Effect.Inclusion
open import Effect.Logic

-- Handlers and elaborations give semantics to programs with (higher-order)
-- effects
open import Effect.Base
open import Effect.Handle
open import Effect.Elaborate

-- Effect theories for first and higher-order effects, to support reasoning
-- about lawfulness of and effect's implementation
--
-- Adapted from the exposition in "Reasoning about Effect Interaction by Fusion,
-- Zhixuan Yang and Nicholas Wu"
open import Effect.Theory.FirstOrder
open import Effect.Theory.HigherOrder 


{- Effect instances -} 

-- Empty effect
open import Effect.Instance.Empty.Syntax 

-- Abort
open import Effect.Instance.Abort.Syntax
open import Effect.Instance.Abort.Theory
open import Effect.Instance.Abort.Handler

-- State
open import Effect.Instance.State.Syntax 
open import Effect.Instance.State.Theory
open import Effect.Instance.State.Handler 

-- Reader
open import Effect.Instance.Reader.Syntax
open import Effect.Instance.Reader.Theory
open import Effect.Instance.Reader.Handler

-- Exception catching
open import Effect.Instance.Catch.Syntax
open import Effect.Instance.Catch.Theory 
open import Effect.Instance.Catch.Elaboration 

-- Lambda
open import Effect.Instance.Lambda.Syntax
open import Effect.Instance.Lambda.Theory
open import Effect.Instance.Lambda.ElaborationCBV

-- Reader w/ local
open import Effect.Instance.LocalReader.Syntax
open import Effect.Instance.LocalReader.Theory
open import Effect.Instance.LocalReader.Elaboration


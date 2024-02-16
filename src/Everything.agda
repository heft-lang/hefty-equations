{-# OPTIONS --without-K #-} 

module Everything where

open import Core.Functor
open import Core.Container
open import Core.Signature
open import Core.Extensionality
open import Core.Ternary
open import Core.MonotonePredicate

open import Effect.Syntax.Free
open import Effect.Syntax.Hefty

open import Effect.Base
open import Effect.Handle
open import Effect.Elaborate
open import Effect.Separation
open import Effect.Inclusion
open import Effect.Logic

open import Effect.Theory.FirstOrder
open import Effect.Theory.HigherOrder 


{- Instances -} 

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
--open import Effect.Instance.LocalReader.Elaboration

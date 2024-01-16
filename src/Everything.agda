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

open import Effect.Instance.Empty.Syntax 

open import Effect.Instance.Abort.Syntax
open import Effect.Instance.Abort.Theory
open import Effect.Instance.Abort.Handler

open import Effect.Instance.State.Syntax 
-- open import Effect.Instance.State.Theory
-- open import Effect.Instance.State.Handler 

open import Effect.Instance.Catch.Syntax
open import Effect.Instance.Catch.Theory 
open import Effect.Instance.Catch.Elaboration 

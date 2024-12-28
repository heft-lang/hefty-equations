# Response

We would like to thank the reviewers for their time and helpful comments!

Below we include inline responses to the comments and questions raised by the
reviewers.

# Changelist

- Expositional improvements to the introduction, based on the helpful
  suggestions by the reviewers.

- Revised 3.5 to clarify relationship with scoped effects.

- Added missing related work on:
  * Lindley et al.'s Scoped Effects as Parameterized Algebraic Theories
  * Schrijvers and Van den Berg's Framework for Higher-Order Effects
  * Kidney et al.'s Algebraic Effects meet Hoare Logic in Cubical Agda
  * Final tagless encodings
  * And more

- Numerous expositional improvements based on the reviewers' suggestions
  (thanks!)

# Detailed response

> Comments to the Author
> # Summary
> 
> It is well-known in the literature that higher-order effects can be simulated
> with algebraic effects and handlers at the cost of broken modularity. Existing
> approaches either lose the separation between syntax and semantics
> (implementing higher-order effects as handling), lose the modularity of
> handler composition (implementing higher-order effects as algebraic effects),
> or require extra mechanisms for composing handlers of higher-order effects
> (the line of work on scoped effects and handlers).
> 
> This paper proposes a simple approach to solving the modularity problem of
> higher-order effects via a modular elaboration of higher-order effects to
> algebraic effects and handlers. The elaboration is achieved by hefty trees and
> hefty algebras, a generalisation of free monads to higher-order functors. The
> elaboration is modular in the sense that the hefty algebras of different
> higher-order effects can be combined together in the same way as combining
> algebras of algebraic effects. Hefty algebras also support modular reasoning
> of correctness with respect to equational theories of higher-order effects.
> 
> This paper is well-written and clearly explains the problems and
> solutions. The idea of elaboration is succinct and works well.
> 
> Compared with the previous conference version, I think the new material on the
> modular equational reasoning approach covers 25% of the paper.
> 
> # Comments
> 
> I have two main comments.
> 
> ## Comparing Hefty Algebras with Scoped Effects
> 
> The line of work on scoped effects and handlers require extra forwarding (or
> weaving) mechanisms for scoped effects. van den Berg & Schrijvers (2023)
> genelise this to higher-order effects. In Section 3.5, the paper discusses
> that hefty algebras are modular in a different way to higher-order effects
> with forwarding. It appears to me that forwarding seems to give a stronger
> notion of modularity than hefty algebras, since it allows us to compose
> handlers together, instead of composing algebras together and putting them
> into one elaboration process. I wonder if the restriction of having one
> elaboration that elaborates all higher-order effects would harm modularity in
> practice.

This is an excellent point. While we indeed tailor the development presented in
the paper to elaborations that elaborate all higher-order effects in one go, we
believe that this is not an inherent limitation of the approach. That is, we
think it is possible to define elaboration with the following signature.

    elaborate : ∀[ Hefty (η₁ ⊕ η₂) ⇒ Hefty (↑ ε ⊕ η₂) ]

This definition of `elaborate` can be used to apply elaborations in sequence, if
we are careful to unify the first-order operations produced by elaborations that
target the same first-order effects. Such a change would, however, require the
carrier of elaboration algebras to be changed from `Free ε` to 
`Hefty (↑ ε ⊕ η₂)`, further complicating the definitions of elaboration
algebras, handlers, and all corresponding proofs.

We agree that forwarding gives a stronger notion of composition.  However, as we
discuss in more detail below, we suspect that it is generally possible to encode
scoped operations as (first-order) algebraic operations.  Furthermore, we
suspect that we can define modular handlers with modular carriers and
appropriate notions of forwarding, to obtain similar modularity benefits as
scoped effect handlers.  Higher-order effect trees provide a syntax of
higher-order operations that we must elaborate into algebraic effects and
handlers that provide appropriate notions of modularity; e.g., using \emph{modular handlers}~\cite{SchrijversPWJ19,DBLP:journals/pacmpl/YangW21}.

We have adjusted the discussion in 3.5 to clarify the points above.

> In Section 4.2, the paper uses sub and jump to simulate the
> transactional semantics derived by swapping the order of handlers with
> scoped effects and handlers. I wonder if it is always possible to do
> so, i.e., if there exists a semantics-preserving encoding from a
> handler sequence of scoped effects (the order of this sequence implies
> the order of handler composition) to hefty algebras such that they
> give the same semantics for scoped effects to the same programs. I do
> not expect this paper to include such an encoding, but I'd like to get
> some intuitions on whether it is possible and how it would work.

Good question again!

We agree that this is beyond the scope of the paper.  Below we elaborate on our
intuition.

We conjecture that there exists a semantics-preserving encoding scoped effects
and handlers, into algebraic effects and handlers.  This conjecture is based on
the observation by Wu, Schrijvers, and Hinze's "Effect Handlers in Scope",
Sect. 7-9, that we can represent scoped operations using explicit markers for
entering and leaving a scope.

To provide some more intuition, we sketch below how we expect a conversion of
scoped effects into algebraic effects could work.

Our conversion uses the following encoding of scoped effects, which is
equivalent (via the co-Yoneda lemma) to the definition of scoped effects we give
in the paper:

    data Prog (Δ γ : Effect) (A : Set) : Set where
      return  : A                                                → Prog Δ γ A
      call    : ⟦ Δ ⟧ (Prog Δ γ A)                                → Prog Δ γ A
      enter   : {B : Set} → ⟦ γ ⟧ (Prog Δ γ B) → (B → Prog Δ γ A) → Prog Δ γ A

First, we can desugar any scoped effect `γ` (encoded as a container in Agda),
into a different effect with explicit operations for entering and leaving a
scope:

    data ScopedOp (Ref : Set → Set) (γ : Effect) : Set where
      sub-scope : Set → Op γ → ScopedOp Ref γ
      sub-end   : (B : Set) → Ref B → B → ScopedOp Ref γ

Here, a `sub-scope B o` operation represents a scoped operation `o`, whose
return type `B` is a value that will be passed to the continuation of a scoped
operation; i.e., the "inner" computation:

    enter   : {B : Set} → ⟦ γ ⟧ (Prog Δ γ B) → (B → Prog Δ γ A) → Prog Δ γ A
                                               ^^^^^^^^^^^^^^^
                                                    inner

A `sub-end` operation represents a marker that we will use to delimit the end of
a scope.  It represents a jump, similarly to the `jump` operation of the
`sub/jump` effect discussed in Sect. 4.2.2.  Specifically, for an operation
`sub-end B c x`, `c : Ref B` represents a pointer to some continuation from
where we should proceed after reaching the end of the scope.  The `sub-end`
operation applies this continuation to a value of type `B`---i.e., `x : B`---to
"jump" to that program point.

Using `ScopedOp`, the following function converts a scoped effect container into
an algebraic effect container:

    conv-Effect : Effect → (Set → Set) → Effect
    Op (conv-Effect Δ Ref) = ScopedOp Ref Δ
    Ret (conv-Effect Δ Ref) (sub-scope B o) = Ref B × Ret Δ o -- Scope
                                            ⊎ B               -- Continuation
    Ret (conv-Effect Δ Ref) (sub-end _ _ _) = ⊥

Here, `sub-scope` has a co-product return type, representing the fact that a
scoped operation is encoded as an algebraic operation that has two possible
continuations:

1. A continuation parameterized by `Ref B × Ret Δ o`, representing a sub-scope
   that will be delimited by a jump (`sub-end`) operation.
   
2. A continuation parameterized by `B`, representing the continuation of the
   sub-scope, which the delimiting `sub-end` operation will jump to.

The following `convert` function uses the `conv-Effect` function and intuition
above to convert scoped effect trees into algebraic effect trees with a scoped syntax:

    convert : {A : Set} {γ : Effect} (Ref : Set → Set)
            → Prog Δ γ A
            → Free (conv-Effect γ Ref ⊕ Δ) A
    convert Ref (return x) = pure x
    convert Ref (call (o , k)) = impure (inj₂ o , λ x → convert Ref (k x))
    convert Ref (enter {B = B} (o , k₁) k₂) = impure (inj₁ (sub-scope B o) , λ where
      (inj₁ (c , r)) → convert Ref (k₁ r) FreeModule.𝓑 λ b → impure (inj₁ (sub-end B c b) , ⊥-elim)
      (inj₂ y) → convert Ref (k₂ y))

As the example in 4.2.2 illustrates, this style of scoped syntax lets us
simulate transactional exception handling.  Intuitively, we expect that this
observation generalizes, and that we can get interaction à la scoped effects in
general, from this style of encoding of scoped effects as scoped algebraic
effect syntax.

Verifying this, and comparing other modularity characteristics, is a topic for
future work.


> ## Modular Reasoning of Higher-Order Effects
> 
> Zhixuan and Wu (2023) proposes a general categorical framework for algebraic
> and higher-order effects with support for equational theories. Lindley et
> al. (2024) proposes a new perspective on scoped effects which enables us to
> reason about scoped effects using parameterised algebraic theories. I wonder
> how the modular reasoning approach in Section 5 is related to these two
> papers. Especially, what are the advantages and disadvantages of reasoning
> with hefty algebras compared to other approaches?

Thanks for the reminders!  We have expanded Sect. 5 to compare with these works.

> # Minor Comments and Typos
> 
> - 121: I would expect `A = () -> C!Δ'` since `A` should be a value type while
>  `C!Δ'` is a computation type

Indeed, thanks! Fixed.

> - 1136: I would use `\citep` for the citation of Levy (2006).
>
> - 1154 1160 1169 1172: There are some `-`s.

Both fixed.

> - 1299: Using sub and jump really feels like cheating to me. I wonder if they
>  are avoidable.

We think you're right that they're avoidable.  We believe the general-purpose
`convert` discussed earlier in this response could be used instead.

> - 1461: "an define"
>
> - 1507: I cannot parse "... the term metavariables respectively return
>  type of the equation".
>
> - 1626: "categorie"
>
> - 1662: "still would"
>
> - 1692: "that establish"
>
> - 2084: the apostrophe of `catch` is different from others

All fixed. Many thanks!


> # References
> 
> Zhixuan Yang, Nicolas Wu:
> Modular Models of Monoids with Operations. Proc. ACM Program. Lang. 7(ICFP): 566-603 (2023)
> 
> Birthe van den Berg, Tom Schrijvers:
> A framework for higher-order effects & handlers. Sci. Comput. Program. 234: 103086 (2024)
> 
> Sam Lindley, Cristina Matache, Sean K. Moss, Sam Staton, Nicolas Wu, Zhixuan Yang:
> Scoped Effects as Parameterized Algebraic Theories. ESOP (1) 2024: 3-21


--------------------------------------------------------------------------------

> Referee: 2
> 
> Comments to the Author
> # Summary

> The paper studies a modularity problem with handling higher-order effects,
> where arguments of effect operations may be computations with scoped
> effects. Scoped effect handlers proposed by Wu et al. address a similar
> problem, but they have limitations such that they require some glue code to
> resolve type mismatch and reject implementations of some higher-order
> effects. As a solution that overcomes the limitations of scoped effect
> handlers, the paper proposed hefty trees, which are effect trees built using a
> higher-order signature functor, and hefty algebras, which elaborate hefty
> trees into effect trees built using a first-order signature functor. 

Good summary.  We would add that another difference from scoped
effects is that some higher-order operations are not scoped
operations, such as operations for constructing effectful lambdas
(see, e.g., the discussion in 2.6.4).

> Based on the development of hefty trees and algebras, the paper also provides
> an infrastructure for equational reasoning about computations with
> higher-order effects and handlers elaborating them. The proposed framework is
> presented based on the development on Agda.

> # Assessment
> 
> I find the following strengths in the paper.
> 
> - The paper includes the formalization of algebraic effects and handlers,
>   scoped effects and handlers, and hefty trees and algebras on Agda. This
>   structure makes the paper readable and clarifies the differences among
>   algebraic effect handlers, scoped effect handlers, and hefty algebras, as
>   well as those among the effect tree representations that the handlers or
>   algebras address. Significantly, the paper clearly describes the limitations
>   of algebraic and scoped effect handlers, why a new framework is necessary,
>   and how the proposed framework, hefty trees and algebras, resolve the
>   limitations. The presentation based on the development on Agda would
>   contribute to avoiding the misunderstanding or ambiguity on the technical
>   part (provided that the reader is familiar with Agda; below I will describe
>   the points that may confuse someone who is, like me, unfamiliar with Agda).
> 
> - The paper builds an equational reasoning infrastructure on top of hefty
>   trees and algebras and shows that it can verify the correctness of hefty
>   algebras with respect to an equational theory. This is a significant delta
>   compared with the conference version.
> 
> Therefore, I'm positive for the technical development of the paper.

Thank you!

> However, I have several concerns about the current form.

We respond to each, and summarize how we have revised the paper to hopefully
clarify where the existing explanations seem to have been lacking.

> The first concern is about high-level contributions of the paper. To describe
> the concern more specifically, recall the elaboration of the operation censor
> (line 169):
> 
>  censor f m = do (x,s) <- (with hOut handle m); out (f s); return x
> 
> where hOut is the handler for the operation out.
> 
> If I understand correctly, the paper says that implementing censor as the
> above _function_ results in losing the modularity benefit of algebraic
> operations. I agree with this claim, but it seems possible to implement censor
> as an _algebraic operation_ in a language with algebraic effect handlers and
> recursive functions:
> 
> let rec f' g = with hCensor handle (g ())
> where hCensor = handler { (return x)      -> return x
>                           (censor f m; k) -> do (x,s) <- (with hOut handle (f' (λ(). do m))); out (f s); k x}
>
> The recursive function f' takes a thunk g that may perform censor, and
> executes g under the handler hCensor for censor. The censor case in hCensor
> runs a computation argument m under hOut and hCensor enabled by the recursive
> call of f' (this enabling may be reminiscent of the encoding of deep effect
> handlers through shallow handlers (Daniel Hillerström and Sam Lindley,
> "Shallow Effect Handlers", APLAS 2018)). Note that f' can be polymorphic over
> the return type of g, so the application f' (λ(). do m) could be typed
> whatever the type of m is.

Could you elaborate on what type `censor` has in your example?

Based on your comment below, it seems you assign it the following type (in
Agda-inspired syntax):

    censor : ∀ {A} → (String -> String) -> (A ! Censor,Output) -> (A ! Censor)

This type restricts sub-trees of the `censor` operation to _only_ contain
operations of type `Censor` and `Output`, which is not modular.  Higher-order
effect trees (`Hefty` trees) admit sub-trees that have effects other than
`Censor` and `Output`.

Another option for how to type `censor` is to use some concrete effect row `Δ`:

    censor : ∀ {A} → (String -> String) -> (A ! Censor, Output, Δ) -> (A ! Censor)
    
This type requires us to apply the handler for `censor` as the first handler,
which has the problems we explained on line 131 in the introduction of our
paper.  To summarize, if we do not apply it first, then either:

(1) `Δ` will contain _more_ effects than the rest of the tree, which means we
    must manually apply handlers to make the sub-tree match the effects of the
    surrounding computation, which is non-modular.

(2) `Δ` will initially contain _fewer_ effects than its surrounding context,
    which means we cannot type all programs we want.

We have adjusted the explanation in the introduction to hopefully reduce
confusion.

> Furthermore, as hefty algebras elaborate all higher-order effects in one go,
> we should be able to assume that m performs no effect operations other than
> censor.

We hope the adjusted phrasing in the introduction has clarified this confusion too.

No, higher-order effect trees can contain multiple effects, so the `m` in
`censor f m` can perform effect operations other than `censor`.  As summarized
on line 223 of the paper, the so-called "smart constructor" (Sect. 2.2) for
`censor` has the following type:

    censor : (String -> String) -> A !! H -> A !! H
                                       ^^^       ^^^
                           sub-computation       effects of the context
                                   effects       the operation occurs in

Here `censor` is polymorphic in the higher-order effect row `H`, and the effects
in the sub-computation matches the effects of the context the operation occurs
in.

We have revised the explanation of higher-order effects in Sect. 1.2 to
hopefully make this clearer.

> Thus, the function f' with hCensor seems able to handle censor performed by g
> in the same way as the hefty algebra eCensor. Because censor is an algebraic
> operation, it could retain the benefit of modularity.
>
> Does the above f' do the same thing as eCensor as I expect?

Not as far as we can tell, for the reasons summarized above.

We hope the revised explanations in the introduction help clear up confusion.

> If it is not, I would like to see a discussion that exposes the critical
> difference between f' and eCensor. Otherwise, what contributions the authors
> can claim compared with existing languages that can accommodate the above
> encoding (thus, can fold higher-order effect trees into first-order effect
> trees)? Perhaps Koka and Frank would be such languages as they support
> higher-order effects (line 2143) and recursion. I guess the contributions may
> be discovering some pattern of effect handlers for higher-order effects,
> giving a formal model characterizing the pattern, and formalizing it on Agda,
> but I'm not sure. I think clarifying such or (if any) other contributions
> helps identify where the paper is positioned in a broader context of the
> research on effect handlers, not just the proposed solution is more beneficial
> than scoped effect handlers.

If we use shallow handlers, it seems we can indeed get similar modularity
benefits as hefty algebras, as that could allow us to use a type of `censor`
akin to the following:

    censor : ∀ {A Δ} → (String -> String) -> (A ! Censor, Output, Δ) -> (A ! Censor)

(Ignoring for now the fact that this operation requires quantifying over effect
trees in operations, which may give rise to universe size issues that make this
style of operation non-trivial to encode in, e.g., Agda.)

It seems a shallow handler for a `censor` operation with the type above could
leave `Δ` completely polymorphic, and simply forward the effects to its
surrounding context, to obtain a similar effect as our elaboration algebras.

On the other hand, it is less clear to us how modular equational theories for
shallow handlers would look and work.

If you have pointers, we would also be happy to learn more about what
higher-order effects Koka supports in practice.  We have found claims to this
end online, but have struggled to find a precise characterization in the
literature.

> Another concern is that the explanation of the modularity problem with
> higher-order operations (Section 1.2) is unclear to me. The paper first
> reminds the readers that "effect handlers are not applied recursively to
> parameters of operations" (lines 122--126). This is a good reminder, but its
> implication (lines 127--129) is unclear.

The implication is that the only way to handle these effects, is to apply a
handler in-line, which is non-modular.

We have adjusted the explanation to explain the problem more directly.

> Why the only way to ensure the argument v has the type whose effects match
> those of the operation clause is to apply handlers of higher-order effects
> before applying other handlers? Why can programs contain at most one
> higher-order effect? What happens if we apply the effect handler closest to
> the operation call? (Since effect handlers, as well as hefty algebras,
> presented in the paper assume to provide some implementations with all the
> effects that handled computations may perform, the closest effect handler
> should be able to handle all the operations including higher-order ones.)
>
> In summary, the latter half of the first paragraph of Section 1.2 confuses
> me.

The point of the paragraph your questions are about is that encoding
higher-order effects in terms of computations in values higher-order effects are
sensitive to the order in which they are applied.

We have revised the paragraph to clarify this.

> The confusion also causes me to be unconvinced about the second
> paragraph. Specifically, I am not sure what "this restriction" (line 134) is
> and why the computation parameters of higher-order operations must be
> continuation-like (lines 134--135).

Perhaps "restriction" is somewhat of a misnomer in this context.  The seminal
work on algebraic effects and handlers by Plotkin and Power (2003) and Plotkin
and Pretnar (2009) defines the syntax of effects such that operations are first
order, i.e., they cannot have any parameters that are themselves computations
unless the effects of these computations are hardcoded in the definition of the
operation, which violates modularity. Only if computational parameters of an
operation behave like a continuation can we represent them using algebraic
effects and handlers, by storing the computational parameters as continuations.

The paragraph has been updated to clarify this.

> For the equational reasoning, the paper shows what equational laws can be
> proven, but does not discuss what cannot be. I think demonstrating the ability
> to reject invalid laws is also important to make it convincing that the
> equational reasoning system is well defined because only "proving" laws is
> possible even in the reasoning system that admits any law.

It is in principle possible to do this, though we are not sure what kind of laws
you want to disprove. It is customary for equational theories to comprise laws
that do hold.

> Also, while the paper explains most of Agda's notations, more notes would be necessary for readers not very familiar with Agda. Specifically, explaining the following notations would be helpful and make the paper more self-contained.
> 
> - L330: Σ (Op Δ) λ op -> ...: Is this a dependent sum type like Σ op : (Op Δ) . ...?
> - L421--422: ∃  λ Δ' -> ...: Is this an existential type ∃  Δ'. ...?
> - L511: λ where ...: Is this a lambda abstraction that does pattern-matching against arguments?
> - L512: flip: It is explained on page 16, but too late.

Fixed, thanks!

> - L678: (k : ...) (r : G C) -> ...: Does this just mean ... -> G C -> ... except that k and r may be referred to in the return type (i.e., the latter "...")? If so, why are k and c named here even though they are not referenced?

Yes.

> - L1027: {| w = w |}  Here, does it mean the argument for w is explicitly given, but the argument for u is omitted?

As remarked in footnote 26, instance argument resolution in Agda needs a bit of
help to type check some of the definitions in our paper.  We omit this helper
code from the paper to aid readability.  The `⦃ w = w ⦄` here was an artifact of
us helping Agda in a hidden code block that we did not show in the paper.  We
have removed the argument in the paper now.

> - L1555: What is a "constructor" in record?

We have added a footnote.

> - L1688--1690: T occurs free. Is it implicitly universally quantified in each line?
> - L1780: A and B occur free. Why is it okay? Isn't it universally quantified?

These are implicitly universally quantified, following the same convention as we
use throughout the paper.  We mention the convention on line 113 of the paper.

> - L1785--1786: What do { A = A }, { Δ' = Δ }, and { γ = k } mean?

These are implicit parameters that we pass explicitly.  We have added a footnote
where we first use implicit parameters.

> - L1809--1812: What do Level.Lift and Level.Lift sl 0l mean?
> - L1838: What does lift mean?

We have added a footnote.

> Finally, I think the presentation of the paper needs to be improved. The issues I found are the following.
> 
> - L53: "as argument" --> "as an argument"?
> - L117--118: I think the types A and B are the argument and return type, respectively, of op, but it is not described, so what A and B are is unclear.

Fixed.

> - L120 "it is only k whose ...": What is "it" here? Perhaps what the sentence wants to say is "only k has a type compatible ..."?

Revised.

> - L231: For the type of hOut', adding parentheses like "(String -> String) -> _(_ A ! Output, Δ => (A * String) ! Δ _)_" would help reading.

It is standard for the arrow to be right-associative.  However, we have simplified this signature away now.

> - L236: "do x <- " -> "do (x,s) <- "

Indeed, thanks!  Fixed.

> - L344 :"We co-products" --> co-product?

Adjusted.

> - L646-651: It is difficult to understand the intuition of the enter constructor in the current form. It would be helpful to give here an instance that illustrates how the enter constructor is used, specifically, how computation arguments and continuations are represented as a term of the type "Prog Δ γ (Prog Δ γ A)"  to express some examples shown in Section 2.6.2. I guess outer computations mean computation arguments and inner ones mean continuations, but they are not explained so clearly.

The `CatchOp` immediately after this is an example.  There's also a forward
pointer to 2.6.2, and there are pointers to the existing work where this
definition is from.

> - L706--710: This part is confusing and needs to be clarified, partly because it is unclear which parts in line 704 correspond to sc, B, and (G B), respectively. Exposing the types of subterms of the argument of the enter constructor might be helpful.

We agree that the types here are a little subtle.  We do not see an optimal way
to expand the types without belaboring the point.  We would like to emphasize
that this part of the paper is only there to add some background that is not
strictly needed to understand our paper.

> - L720--725: This is also confusing as m1 and m2 do not appear in the code and the continuation is specified by k in the main text but I think the continuation in the code should correspond to f. I suspect the explanations in lines 706--710 and 720--725 are for the code in the conference version and are not updated for the submitted article.

Thanks, adjusted.

> - L916: The motivation to consider the question of how to address computation parameters with polymorphic return types is unclear at first glance.

We hope they become clear in the relevant section that the sentence here is referencing.

> - L963: It is not clear why "using a type universe" is more natural in modeling types as an interface of programming.

Pattern matching on types in Agda (or most type theories) is disallowed.  For
some elaborations, this is useful and/or needed.  This is possible, if we use
type universes.

This is a somewhat technical point that did not come across clearly.

We have adjusted to simply say we use type universes now.

> - Page 22: Please give a concrete instance of Univ.

We have added a forward pointer to S4.1.

> - Page 26: Many inappropriate hyphens are inserted, like "- Here `lam is" (line 1154)
> - L1172: "interpretation [to] `lam"
> - L1180: "matches [that of] the function type"
> - footnote 26: The isomorphism has been explained in footnote 17.

Thanks, fixed.

> - L1294: Why the contents type of Ref is τ, while the argument type of k is [[ τ ]]?

The sentence a few lines later explains: `Ref t` represents a continuation
expecting a value of type `[[ t ]]^T`.

> - L1325: It is unclear what "invoking a handler before another handler" means.
> - L1368: "definition" --> defined?

Thanks, fixed.

> - Page 32. It is not clear how interleave is implemented. This makes me feel why the algebra of eConcur for atomic is given by `sub (λ ref -> ψ tt >>= `jump ref) k. It seems the same as ψ tt >>= k due to the second law of sub/jump (line 1302), no?

The artifact provides the source code.

> - L1445: "An effect and its laws is" --> An effect and its laws constitute?
> - L1457: "get operation[s]"
> - L1461: "We [c]an define"
> - L1506: "the fields Γ and R define the term metavariables respectively return type of the equation  I cannot read. Please consider rephrasing.

Thanks, fixed.

> - L1508: Please explain what unapplied substitutions are.

The remarks here did not add much that the previous sentence did not say
already.  We've removed the sentences, shortening the distance to the example
which illustrates how `Γ` and `R` are used.

> - L1515--1519: "the return type of the program on ... should be equal to this type metavariable." What do you mean by the return type of the program? The type of the program should be N -> Free State A, not the type metavariable A.
> - L1676: "As discussed"  Where?

Thanks, adjusted.

> - L1681: "where necessary" --> where it is necessary?

Everywhere we use the modal necessity.

> - L1852: What is "abeq"?
> - L1922: "We can define the same reasoning combinators"  As what?
> - L1955: "Catch effe[ct]"

Thanks, fixed.

> - Section 5.8: Why isn't the equation for first-order effect trees parameterized over the equality of the remaining effects?

We do not understand the question.  Could you paraphrase?

> - L1994: The meaning of inj^H { X = A} m is not clear.

Footnote added.

> - Many citations need more appropriate parentheses, such as "Levy's call-by-push-value Levy (2006)" --> "Levy's call-by-push-value (Levy 2006)". Similar issues are found in:
>  - L1160
>  - L1257
>  - L1275
>  - L1367
>  - Section 6

Thanks, fixed.

> Referee: 3
> 
> In this paper, the authors introduce "hefty algebras," a generalisation of
> algebraic effects to higher-order operations that utilise their computational
> arguments in a non-algebraic way (i.e., not as continuations that commute with
> the evaluation context). This approach is similar to scoped effects, but hefty
> algebras interpret operations in two stages: in the first stage, higher-order
> operations are elaborated (i.e., term-expanded) into computations using
> standard algebraic effects, which are then further interpreted through
> handlers in the second stage.
> 
> After summarising ordinary algebraic effects and handlers, the paper
> demonstrates how to generalise this approach to higher-order operations and
> how such elaborations can be composed. Next, the paper provides several
> examples that highlight the modularity of this approach and develops an
> equational logic for specifying higher-order operations and validating their
> elaborations. This development generalises established reasoning techniques
> for algebraic effects and is the primary addition to this version from the
> conference presentation.
> 
> As in the original version, the entire paper, including the new developments,
> is formalised in Agda. I commend the effort; having an Agda formalisation is a
> significant asset. However, I would still appreciate it if more of the
> development were done independently of Agda, as even with all the pretty
> notation that Agda provides, the reader can easily become lost in the
> encodings.

We appreciate your reading efforts!

We have tried to communicate the gist of our idea informally, in non-Agda
syntax, in the introduction, and the categorical gist of our solution in the
opening paragraphs of Sect. 3.

If you have more ideas for expositional improvements, we would be happy to
consider them.

> Given that the work on hefty algebras has been accepted at a major conference,
> I assume the community finds it interesting and meaningful. The additions in
> this version are significant enough to consider it for journal
> acceptance. However, I cannot shake the feeling that the approach introduces a
> roundabout and unnecessary way of achieving modularity through a variant of
> handlers.
>
> The two distinguishing features of handlers are dynamic scoping and their
> exclusive application to continuations. Without the latter, we unfold
> operation definitions everywhere, which is exactly what the usual binding
> constructs already accomplish.

Indeed!

Except, unlike many usual binding constructs, we want the unfolding to be
given compositionally.

> With scoped handlers, the programmer at least has control over the level at
> which interpretations are applied (as described from line 1101 onward). In
> contrast, with hefty algebras, one must unfold elaborations of all
> higher-order operations at the same time (line 1113), and I struggle to see
> the advantages of this approach.

Advantages:

1. As discussed in Sect. 2.6.4, effectful functions and other thunking
   constructs are not scoped effects.  As we demonstrate in Sect. 4.1, our
   approach provides a relatively simple syntax and semantics of them.

2. Algebraic effects provides at least some of the same control we get from
   scoped effects already, as our example in Sect. 4.2 demonstrates, and as we
   also discuss in our response Reviewer 1.
   
3. When we do not need this control, algebraic effects are sufficient.  Indeed,
   it is not clear to us that it is necessarily a good thing that we have to
   think deep and hard about the order we apply handlers in.  If, for example,
   we wanted our approach to be used by domain-specific language engineers, it
   seems helpful if they can apply handlers in any order and get the intended
   semantics; i.e., if the composed (higher-order) effect theories happen to
   have a commutative tensor product (Hyland et al., 2006).
   
4. Surprisingly (at least to us), these advantages fall out of applying fairly
   standard techniques: folding a free monad over a higher-order signature
   functor into the "traditional" free monad over a first-order signature
   functor, and then applying standard effect handlers.

> For example, in line 175 (and later in line 578), you state that you can
> refactor the semantics of a program only by modifying or copying
> code. However, instead of using higher-order operations, you could employ
> well-established higher-order functions and define `censorHello` as:
> 
>    censorHello = λ(censor : (String → String) → (A!Δ,Out → A!Δ)).
>      censor (λs. …) hello
>
> Then, instead of the two elaborations, define the functions:
> 
>    eCensor f = do (x, s) ← (with hOut handle m); out (f s)
>    eCensor' f = do x ← (with hOut' f handle m); x
> 
> and use them as:
> 
>    with HOut handle (censorHello eCensor)
>    with HOut handle (censorHello eCensor')
> 
> Such functions would also be naturally polymorphic and would avoid the
> overhead of encoding types through universes, as done in section 3.4. Instead
> of higher-order functions, one could impose even more structure by using
> modules and functors.

This sounds like a so-called _final encoding_.  (Akin to MTL style type classes
known from Haskell.)

Final encodings are indeed an alternative to the initial encoding we use in the
paper.

We have added a discussion of the relation to final techniques to the related
work section.

> CONCLUSION
> 
> Perhaps I am missing something, but I remain reluctant to accept the paper. At
> the very least, I would like the authors to explain what their approach offers
> over established constructs for ensuring modularity—not just in the context of
> effects, but standard ones such as higher-order functions or functors.

We have revised the paper to provide the following explanations:

- Clarifying remarks that it is an a question for future work whether it is
  always possible to encode scoped syntax in terms of algebraic effects and
  handlers.

- Expanded the related work section to discuss the possible alternative encoding
  of our approach, using final tagless techniques.

> MINOR NOTES
> 
> - line 61: A reader would benefit from an example of an effect with multiple operations (e.g., state).

We do not see the essential benefit of using state instead of output at this
point in the paper, but would be happy to hear your reasons for thinking so.

We do say a few lines down that effects can have multiple operations associated
with it.

> - line 68: Point out that this is a type of a specific effect handler for Output.

Thanks, fixed.

> - line 93: Note that the ability to extend a handler type on both sides with Δ₂ does not hold in general. For example, in call-by-value (CbV), a handler returning a thunk of the continuation has the type `A!Δ,Eff ⇒ (⊤ → A!Δ)!Δ`, and extending Δ does not merely extend it on the RHS but also modifies the return type `⊤ → A!Δ`.

The sentence was meant to illustrate how some specific handler could be applied.

We've adjusted the phrasing.

> - line 120: It is not true that only `k` has a type compatible with the RHS; you could also return a value of type `C`.

Thanks, we've adjusted the phrasing.

> - line 129: This reasoning is difficult to follow. Can you provide a concrete example? You could explicitly handle the value `v` by inserting an additional handler, which would clarify the order of handler application.

Reviewer 2 had similar concerns, and we've adjusted the phrasing.

> - line 143: Operations without computation parameters are known in the algebraic effect literature as "generic effects."

Citation added.  Thanks!

> - line 150: All the examples of "operations" you give are actually handlers. What is the rationale for including them under operations if they are of a different nature?

In, e.g., the cited monad transformer library, they are monadic operations, so
we model them as such.

> - line 236: Doesn't `hOut'` already output the modified strings, making `out s` unnecessary (and also ill-typed)?

There was a typo and type error here, thanks.  Fixed!

> - line 327: Why is this called an extension? It does not extend anything but rather represents a syntactic signature as a set construct. Perhaps call it reflection, interpretation, or denotation.

The terminology originates from the original paper on containers by Abbott,
Altenkirch, and Ghani (2005). We are happy to adopt a different terminology if
the reviewers think that improves clarity of the paper.

> - line 330: Σ is never explained.
> - line 344: Typo: "We co-products…" should be "We use co-products…"
> - line 422: ∃ is never explained.

Thanks, fixed.

> - line 492: Why do you restrict handlers only to those targeting the free monad? If you allowed arbitrary codomains given suitable algebras, you could avoid passing around an explicit set of parameters `P`.

We probably could.

We follow the handler setup in, e.g., Wu, Schrijvers, and Hinze's "Effect
Handlers in Scope" (Sect. 4).

We've added a footnote.

> - line 1154: Some redundant dashes appear at the start of this and the following few paragraphs.

Thanks, fixed.

> - line 1185: How is "lam" related to "`lam"? And similarly for other constructs?

We've added the explicit effect signatures to each subsection in Sect. 4.

> - line 1979: Typo: "defintion" should be "definition."
> - line 2054: Missing opening bracket in �� catch.
> - line 2101: The majority of citations in this section are in the incorrect form, i.e., using "Name (YEAR)" instead of "(Name YEAR)" when not referring to authors.

Thanks, fixed.



# Top-level response

Dear Sam,

Thanks for the feedback.

We've revised our paper in accordance with your suggestions.

The most important changes are:

* We have revised the related work paragraphs about Matache et al.'s work on scoped effects as parameterized algebraic theories, in accordance with your suggestion and the suggestion of Reviewer 1.

* We have revised the introduction to nuance our description of the problem we address, using concrete examples where possible.  This revision should help clarify concerns by both R2 and R3:
 
  + R2: Clarified that the paper is proposing a formal semantics for overloading-based definitions of higher-order effects and theories.

  + R3: confusion about what modularity problem the previous introduction was trying to pinpoint.  We have decided to completely rewritten the introduction to clarify, using (a variant of) the calculus from Pretnar's tutorial paper (Pretnar, 2015).

* Furthermore, we have further refined the related work section.  Besides the already mentioned discussion of the work by Matche et al.:

  + We have refined the paragraphs about final tagless to be more precise about how/why the paper uses initial encodings instead of final tagless encodings.
  
  + We have added a paragraph about shallow handlers.

* We have fixed minor typos and issues pointed out by the reviewers.

# Reviews

> Referee: 1
> 
> Comments to the Author

> Thanks for your detailed response. However, the submitted pdf appears
> to be identical to the previous one. I managed to find an author
> version online at http://www.casvanderrest.nl/jfp-draft.pdf which
> seems to reflect the proposed changes in the response. I'm happy with
> the changes in this online version but I need to get confirmed that
> this version is indeed what the authors intended to submit in order to
> move to accept.



> ## Comparing Hefty Algebras with Scoped Effects
> 
> I agree with the point that it is possible to define elaboration in
> sequence. I believe this change would as a result require extending
> elaboration algebras with forwarding clauses similar to those in
> scoped effect handlers. Correct me if I misunderstood what you meant.
> 
> I'm happy with the new discussion in Section 3.5.
> 
> ## Encoding Scoped Effects into Algebraic Effects
> 
> Thanks for the insightful encoding. It makes sense to me that this
> encoding indeed transforms a computation tree with scoped effect `γ`
> to another computation tree with algebraic effect `conv-Effect γ Ref`
> which explicitly annotate the start and end of the scopes of all
> scoped operations in `γ` with algebraic operations `sub-scope γ` and
> `sub-end γ`. This step is very nice and indeed corresponds to the idea
> in Sections 7-9 of Effect Handlers in Scope.
> 
> However, I failed to see how this transformation connects to the
> example in Section 4.2.2. The example in Section 4.2.2 uses jump to
> jump to the handling branch of catch, which is still a computation in
> the scope of catch. This is different from `sub-end` given by the
> translation which jumps out of the scope. For instance, consider the
> algebraic effect `conv-Effect Catch Ref`, I would expect its handler
> is defined in a similar style to `bcatch` and `ecatch` in Section 9 of
> Effect Handlers in Scope instead of that in Section 4.2.2. Did I
> misunderstand something?
> 
> Nonetheless, I believe this encoding would work for a range of
> examples, though I think the translation from a handler for scoped
> effect `γ` to a handler for `conv-Effect γ Ref` is not that obvious
> and it is dubious whether it always exists. I believe all these belong
> to future work and I'm looking forward to a full specification of this
> approach in a future paper.
> 
> This encoding does not seem to rely on anything relevant to Hefty
> algebras and an elaboration stage. I have a new concern relevant to
> the elaboration in Section 4.2.2. I think the elaboration does not
> change the fact that the handler `hThrow` is always applied first to
> `m1`. It is perhaps fine for this example, but may be problematic for
> others, e.g., the non-determinism in Section 4.3. This is because even
> only considering `or` and state operations, there are already global
> and transactional/local semantics provided by swapping their handlers.
> I don't think the technique in Section 4.2.2 would work if we want to
> implement the transactional semantics in the presence of `once`,
> because the elaboration of `once` would force `hChoice` to be applied
> first, giving the global semantics. (I believe the encoding with
> sub-scope and sub-end should be able to give the transactional
> semantics.)
> 
> ## Modular Reasoning of Higher-Order Effects
> 
> Thanks for the new discussions. I'm happy with them. One minor point
> is I'm not sure some description of Lindley et al. 2025 /
> parameterised algebraic theory is accurate. For instance, I think
> parameter variables instead of computation variables denote scopes.
> 
> Referee: 2
> 
> Comments to the Author
> The authors have improved their presentation and suitably resolved most of my outstanding issues. I continue the discussion of the remaining ones below. However, I remain unconvinced.
> 
> The main aim of the paper is _modular_ elaboration of _higher-order_ operations. That is, can we separate the specification of some higher-order operation (catch, spawn, …) in a way that multiple implementations can be developed independently and used at a later time? We all agree that algebraic effects and their handlers achieved this for multiple first-order operations, and scoped effects extended it further higher-order examples, but both approaches have their limitations.
> 
> Hefty algebras achieve this by collecting all higher-order operations and unfolding them all at once. But I do not want to constrast this with algebraic/scoped effects. The latter two both crucially allow staged unfolding, which then leads to the above limitations. What I am interested in is the difference to existing mechanisms for simultaneous unfolding such as signatures/modules, final encoding, records, … You do now mention these in the related work section, but I am missing the discussion of their advantages or disadvantages. Were these existing, well-understood, approaches not modular in some sense? (You hint at this with "Except, unlike many usual binding constructs, we want the unfolding to be given compositionally.") Does the newly introduced reasoning logic bring any new insights?
> 
> I will not oppose publication, but I am likely not the only reader with these reservations. Let me rephrase them, as it is important for the authors to address them -- or my misinterpretation -- in the paper.
> 
> ---
> 
> > > - line 61: A reader would benefit from an example of an effect with multiple operations (e.g., state).
> >
> > We do not see the essential benefit of using state instead of output at this
> > point in the paper, but would be happy to hear your reasons for thinking so.
> >
> > We do say a few lines down that effects can have multiple operations associated
> > with it.
> 
> I did not mean to replace the nondeterminism example with the state one. Just that in the comment mentioning multiple operations (line 60), briefly give an example of an effect with more than a single operation. For example
> 
> > An effect can generally be associated with multiple operations (but not the other way around);
> > for example, state has an operation _get_ for reading and _set_ for writing the memory;
> > however, the simple _Output_ effect that we consider is only associated with the operation _out_.
> 
> ---
> 
> > > - line 68: Point out that this is a type of a specific effect handler for Output.
> >
> > Thanks, fixed.
> 
> Instead of "a specific type of an effect handler for Output" I would suggest "a type of a specific effect handler for Output" since that implies that there are multiple handlers for Output with multiple different types, while the the former suggest that there is a particular type for all Output handlers.
> 
> ---
> 
> > > - line 120: It is not true that only `k` has a type compatible with the RHS; you could also return a value of type `C`.
> >
> > Thanks, we've adjusted the phrasing.
> 
> This is still incorrect, `c` could also perform some effects from `Δ'` and then return `w : C`. So `c` will eventually return a value `w`, but is not equal to `return w`.
> 
> ---
> 
> > > - line 150: All the examples of "operations" you give are actually handlers. What is the rationale for including them under operations if they are of a different nature?
> >
> > In, e.g., the cited monad transformer library, they are monadic operations, so
> > we model them as such.
> 
> Of course, but one of the main insights that algebraic approach provided was that monadic operations naturally split into effect constructors (i.e. algebraic operations, which satisfy the algebraicity property) and effect deconstructors (i.e. handlers, which are homomorphic over the operations). Trying to re-merge the two classes is only a source of confustion.
> 
> ---
> 
> line 360: "dependen[t] sum"
> 
> ---
> 
> line 370: "For example, [t]he effect"
> 
> 
> Referee: 3
> 
> Comments to the Author
> Thank you for the response. The presentation has been improved, but my concerns remain.
> 
> # Response to Response
> 
> > Could you elaborate on what type `censor` has in your example?
> 
> I suppose the following, same type as the one presented in the paper:
> 
>  censor : ∀ {A} →∀ {Δ} → (String -> String) -> (A ! Censor, Δ) -> (A ! Censor, Δ)  -- (1)
> 
> > Based on your comment below, it seems you assign it the following type (in Agda-inspired syntax):
> > censor : ∀ {A} → (String -> String) -> (A ! Censor,Output) -> (A ! Censor)
> 
> > Another option for how to type `censor` is to use some concrete effect row `Δ`:
> > censor : ∀ {A} → (String -> String) -> (A ! Censor, Output, Δ) -> (A ! Censor)
> 
> I am not sure why `Output` is added to the effect row of the second argument, although it is not present in the type presented in the paper (lines 115-116 in the revision).
> 
> > Another option for how to type `censor` is to use some concrete effect row `Δ`:
> 
> > (1) `Δ` will contain _more_ effects than the rest of the tree,...
> 
> I am unsure why the authors consider some _concrete_ effect row `Δ` in the response.
> Cannot type (1), which universally quantifies Δ, be given to `censor` in the initial review? If so, why not, and why can only the `censor` given in the paper have the type?
> (From the comment to shallow handlers, it seems that the authors consider _deep_ handlers could not leave `Δ` polymorphic, but I am not sure why.)
> 
> > (2) `Δ` will initially contain _fewer_ effects than its surrounding context,
> > which means we cannot type all programs we want.
> 
> It would be helpful to present a concrete program that the authors want but cannot be typed.
> 
> >> Furthermore, as hefty algebras elaborate all higher-order effects in one go,
> >> we should be able to assume that m performs no effect operations other than
> >> censor.
> 
> > No, higher-order effect trees can contain multiple effects, so the `m` in
> > `censor f m` can perform effect operations other than `censor`.
> 
> It may have been difficult to understand, but I did not mean a _call_ `censor f m` cannot perform effect operations other than `censor`; I mean that, given a handler that only handles `censor`, since I suppose `censor` has type (1), it turns out to be Δ = `Censor`, so _the parameter `m` passed to the `censor` handler_ can only perform `censor`. Note that the original comment is given for the following handler code:
> 
>  let rec f' g = with hCensor handle (g ())
>  where hCensor = handler { (return x)      -> return x
>                            (censor f m; k) -> do (x,s) <- (with hOut handle (f' (λ(). do m))); out (f s); k x}
> 
> (Perhaps Δ might be `Censor, Output` and the handler should handle `out` correctly for allowing `m` to output some strings.)
> 
> 
> >> Thus, the function f' with hCensor seems able to handle censor performed by g
> >> in the same way as the hefty algebra eCensor. Because censor is an algebraic
> >> operation, it could retain the benefit of modularity.
> 
> >> Does the above f' do the same thing as eCensor as I expect?
> 
> > Not as far as we can tell, for the reasons summarized above.
> 
> > We hope the revised explanations in the introduction help clear up confusion.
> 
> For the above reason, the response has not resolved my concern.
> 
> 
> > If we use shallow handlers, ...
> 
> I believe that the (more detailed) discussion on shallow handlers is valuable and should be described in the paper.
> Specifically, the paper should clarify why (only) shallow handlers could obtain a similar effect as elaboration algebras and (maybe) why deep handlers could not.
> 
> > If you have pointers, we would also be happy to learn more about what
> > higher-order effects Koka supports in practice. We have found claims to this
> > end online, but have struggled to find a precise characterization in the
> > literature.
> 
> I do not know, unfortunately. I realized the support for higher-order effects in Koka just by reading this paper.
> 
> >> Another concern is that the explanation of the modularity problem with
> >> higher-order operations (Section 1.2) is unclear to me. The paper first
> >> reminds the readers that "effect handlers are not applied recursively to
> >> parameters of operations" (lines 122--126). This is a good reminder, but its
> >> implication (lines 127--129) is unclear.
> 
> > The implication is that the only way to handle these effects, is to apply a
> > handler in-line, which is non-modular.
> 
> > We have adjusted the explanation to explain the problem more directly.
> 
> The adjusted explanation is clearer. I appreciate it, but I hope the following are also clarified.
> 
> - L123-124: "the left and right hand sides of handler cases"  Does the left hand side mean parameters and continuations, and the right hand side mean the body term?
> - L143-145: "If we apply more handlers of effects contained in the value v, ..."  Please consider adjusting this sentence. I'm confused due to the following points:
>  - More than what?
>  - Why must the handler of `op v` eventually explicitly apply handlers for "those"?
>  - How is this related to "the sensitivity of the order of applying handlers"?
> - L145-146: "This sensitivity to the order of ... non-modular"  If I understand correctly, the only modularity mentioned in the paper (up to here) is the capability of refining the meaning of effect operations (such as `out`) without modifying programs that call the effects (such as `hello`). Does the paper mean the sensitivity of the order of applying handlers breaks this specific modularity? If so, why? I agree that the insensitivity is desirable, but I'm not sure why the sensitivity leads to breaking the modularity, i.e., disallows refining the meaning of effect operations without modifying programs that call the effects. Of course, handlers may need to be adjusted (e.g., to re-apply other handlers), but the programs calling the effects themselves seem able to be unchanged. Or do the authors refer to another kind of modularity? Also, I think giving concrete examples would help one understand the point of the problem.
> 
> > It is in principle possible to do this, though we are not sure what kind of
> > laws you want to disprove. It is customary for equational theories to comprise
> > laws that do hold
> 
> I would like just to see the inconsistency of the given infrastructure for equational reasoning. For example, given an equational theory for states, `put s >> put s' \equiv put s` should be disproven (unless s is equal to s').
> 
> 
> # Other Comments
> 
> - L227-231: Here, the type of `censor_op` is given as `(String -> String) -> A !! H -> A !! H`, but its type given in Figure 2 is `(String -> String) -> Hefty (Censor + H) T -> Hefty (Censor + H) T`. So, the correct type in line 227 should be `(String -> String) -> A !! (Censor + H) -> A !! (Censor + H)`?
> 
> - Section 3.2: No elaboration for eCensor is given, although it is a motivating example presented in Section 1. The absence of eCensor makes it unclear how hefty trees and elaboration resolve the problems mentioned in Section 1.
> 
> - Section 3.5: While scoped effect handlers can be applied one by one, hefty algebras enforce elaborating all the higher-order operations at once. Please discuss whether this is problematic and, unless so, why.
> 
> - L1142-1143: "h1, ..., hk in (‡)" --> "h1, ..., hk in (§)",  "h1', ..., hn' in (§)" --> "h1', ..., hn' in (‡)"
> 
> - L1456: "signature is given in ??"


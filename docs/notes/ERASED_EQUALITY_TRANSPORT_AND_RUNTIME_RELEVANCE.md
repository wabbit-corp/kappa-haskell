# Erased equality transport and runtime relevance

Date: 2026-08-05

Status: open specification decision

## Executive summary

The current specification distinguishes erased equality induction from
proof-relevant equality transport, but it does not completely define the
boundary between them. This becomes visible when comparing these two staged
fixtures:

- `tests/pending-import/spec-coverage/application-dotted/transport-runtime-relevance.kp`
- `tests/pending-import/spec-coverage/patterns-active/erased-equality-proof-match.kp`

The first fixture correctly requires the elaborator not to *silently* insert a
runtime transport using an unrestricted, potentially proof-relevant equality:

```kappa
relevantBad :
    forall (@0 a : Type) (@0 x : a) (@0 y : a).
    (ω p : x = y) -> GenericBox a x -> Unit

let relevantBad @a @x @y (ω p : x = y) (box : GenericBox a x) : Unit =
    needsGeneric @a @y box
```

Section 16.1.8 says that the implicit `subst` required at the call is not
portable unless the proof is known `RuntimeErased`, the transport occurs under
ambient demand `0`, or the proof-relevant transport has a specified backend
lowering. None of those premises holds here.

The second fixture asks for explicit erased equality induction:

```kappa
cast0 :
    forall (@0 a : Type) (@0 b : Type).
    (0 p : a = b) -> a -> b

let cast0 p v =
    match p
    case refl -> v
```

Section 17.1.3 appears to accept this because the match performs no runtime
discrimination of `p`; its single branch uses equality induction to refine the
type of `v`. Section 31.2 similarly says that erased `subst` and `pathInd`
compile as type-directed coercions rather than runtime branches.

The apparent inversion is real: `cast0` still transports a runtime value from
type `a` to type `b`. Calling that operation "only a type refinement" does not
by itself prove that erasing the transport is sound. The specification must do
one of the following:

1. guarantee that every equality admitted to erased runtime transport is
   representation-coherent, so the transport may lower to the identity on the
   runtime payload; or
2. restrict erased equality matching so a generic `cast0` is rejected unless
   representation preservation follows from stronger premises.

The recommended portable-v1 design is the first, with a sharply separated
computational-path lane: erased equality induction is a statically checked,
representation-preserving coercion, while proof-relevant or computational
paths require an explicit runtime lowering. The automatic elaborator must
still not silently select erased semantics for an unrestricted proof. This
makes `cast0` and `relevantBad` consistent: they choose different elimination
modes, not different logical powers for erased and non-erased proofs.

That recommendation requires new normative text. The current rules imply much
of it, but never state the representation theorem or the admissibility check
on which it depends.

## 1. The four cases that must be kept distinct

The two fixtures contain more than one kind of equality use. Conflating them
is what makes the behavior seem paradoxical.

| Case | Proof availability | Result/transport demand | Why it should be accepted or rejected |
| --- | --- | --- | --- |
| `sym0` | quantity `0`; `IsSet a` makes the equality proof type `RuntimeErased` | proof result | Accept. Both the input proof and output proof are erased, and there is no runtime payload transport. |
| `forcedRefl` | quantity `0`; endpoints are definitionally `True` and `True` | runtime `Int` result | Accept. The only branch is statically forced to `refl`, and the result is the constant `7`; no runtime coercion or proof discrimination remains. |
| `cast0` | quantity `0`; arbitrary equality between types | runtime value changes static type from `a` to `b` | Accept only if the language guarantees representation-coherent erased transport. The operation is not made sound merely by having one branch. |
| `relevantBad` | quantity `ω`; arbitrary equality between indices | automatic transport of a runtime `GenericBox` | Reject under the current automatic-transport policy. The elaborator may not silently erase or invent a runtime interpretation for a potentially proof-relevant transport. |

Two additional positive cases in `transport-runtime-relevance.kp` test the
other explicit exceptions in §16.1.8:

- `erasedOk` uses equality over `Bool`, whose equality is known
  `RuntimeErased`; and
- `demandZeroOk` transports an argument whose receiving binder has demand
  `0`, so no transported runtime payload survives.

Those cases are independent of the generic `cast0` question and should remain
positive.

## 2. Quantity, proof erasure, and transport mode are different facts

The relevant properties are not interchangeable.

### 2.1 Binder quantity is a capability and usage constraint

`0 p : a = b` says that occurrences of `p` cannot be required by runtime
computation. `ω p : a = b` makes the proof available without such a linear
usage restriction. This is a statement about how a variable may be used, not
by itself a theorem about the runtime representation of its type.

In particular, an unrestricted binder is not logically weaker than an erased
binder. Under the ordinary quantitative reading, a value available at
quantity `ω` can also be used in an erased position. If Kappa rejects an
operation using the `ω` proof while accepting a corresponding operation using
a `0` proof, the explanation must be the selected elimination mode or an
explicit elaboration policy—not that the unrestricted proof carries less
evidence.

### 2.2 `RuntimeErased (a = b)` is a property of the proof type

The equality type can independently be known to have no runtime
representation. For example, `IsSet a` makes equality between inhabitants of
`a` proof-irrelevant in the relevant sense, and the Spec uses this to justify
erasure.

A quantity-`0` binder does not automatically establish
`RuntimeErased (a = b)`. It says that this occurrence is erased. Conversely, a
value whose type is `RuntimeErased` is erased even if its source binder uses a
nonzero quantity, unless explicitly reified by a standardized carrier.

### 2.3 Ambient demand belongs to an occurrence or expression

A transport checked under ambient demand `0` produces no runtime-consumed
result. This is why `demandZeroOk` is safe even though its equality proof is
not known globally to satisfy `RuntimeErased`.

That fact does not apply to `cast0`: its returned `b` is runtime-relevant. The
proof occurrence is erased, but the transported payload is not.

### 2.4 Transport mode is an operational commitment

The same logical equality can participate in two operational modes:

- **erased induction**, which is checked statically and lowers to a
  representation-preserving coercion with no runtime inspection of the proof;
- **proof-relevant transport**, whose behavior may depend on the proof and
  therefore needs a specified runtime implementation.

The language must say how a use selects a mode and why that mode is sound. A
quantity annotation is relevant to the selection, but it is not a substitute
for the representation argument.

## 3. What the current Spec says

### 3.1 Section 11.4.1: equality eliminators and lowering

Section 11.4.1 defines `pathInd` and `subst` and gives two operational modes.
An application is erased when it is checked under ambient demand `0` or when
the equality proof's type is known `RuntimeErased`. A proof-relevant transport
whose result is runtime-relevant must instead be backend-lowerable, for
example because it reduces to `refl`, belongs to a specified computational
path profile, or uses a trusted primitive with defined behavior.

The same section also says:

- equality does not make every proof quantity `0` by definition;
- a source quantity-`0` proof annotation is accepted only when the quantity
  checker can justify that the proof is not required by runtime-relevant
  computation; and
- an implementation must not silently erase a proof-relevant equality merely
  because `refl` is the only visible constructor.

There is a gap between the two named modes. An equality proof can be available
at quantity `0`, while its type is not known `RuntimeErased` and the eliminator
returns a runtime-relevant payload. `cast0` has exactly this shape. Section
11.4.1 does not directly say whether this is erased transport,
proof-relevant transport, or an inadmissible use.

### 3.2 Section 16.1.8: automatic equality transport

Section 16.1.8 makes automatic transport insertion deliberately conservative.
For a runtime-relevant expression, the inserted equality proof must be
`RuntimeErased`, the inserted transport must be checked at demand `0`, or the
proof-relevant transport must already have a backend lowering.

This rule makes `relevantBad` a valid negative test. The call syntax does not
say that the programmer wants to discard the computational content of `p`.
Choosing an erased transport automatically could change the meaning of a
future proof-relevant path, and choosing a proof-relevant transport would
leave an unlowerable runtime operation.

The rule also correctly accepts `erasedOk` and `demandZeroOk` in principle.
The reference compiler currently rejects those two cases, which is an
implementation gap independent of the generic `cast0` issue.

### 3.3 Section 17.1.3: matching an erased equality proof

Section 17.1.3 accepts a source match on a quantity-`0` equality proof when it
elaborates to erased equality induction and needs no runtime discrimination.
It specifically permits a match when:

- the result is under ambient demand `0`;
- the branch only refines types or erased proof obligations; or
- the scrutinee is statically forced to `refl`.

The second bullet appears intended to accept `cast0`. Its match has one branch
and the runtime term returned from that branch is the same payload `v`.

However, the phrase "only refines types" describes the source term, not the
backend invariant. The output expects the calling convention and runtime
representation of `b`, while the input payload has those of `a`. The match
does not inspect `p`, but that alone does not establish that the identity
coercion is a valid lowering.

### 3.4 Section 31.2: erasure

Section 31.2 says that erased `subst` and `pathInd` compile as type-directed
coercion/refinement rather than as runtime branches on proof representation.
It also states that erasure preserves the behavior of the computational
fragment.

This is close to the missing guarantee, but it does not define the premise
under which a type-directed coercion between runtime types is
representation-preserving. It refers the erased-versus-proof-relevant
obligation back to §11.4.1, where the quantity-`0`/runtime-result case is not
classified completely.

### 3.5 Sections 11.5 and 30.2.7: no accidental UIP or path collapse

The Spec intentionally does not assume UIP, and it reserves a future cubical
or computational path lane. It also avoids reasoning that would collapse
distinct proof-relevant transports.

Consequently, the missing rule cannot simply say that every equality proof is
operationally `refl`. The rule must instead identify an erased lane whose
admissible evidence is representation-coherent, while preserving a separate
proof-relevant lane for paths with computational behavior.

## 4. Why the apparent reversal is confusing

It is tempting to summarize the fixtures as:

> Matching an erased proof may change a runtime type, while a non-erased proof
> may not.

That summary would indeed be backwards. The intended distinction is more
precise:

> An explicit erased equality induction may request a statically checked,
> identity-lowered coercion. Automatic elaboration may not silently reinterpret
> a potentially proof-relevant equality as that erased coercion.

This explains the *policy* difference:

- `cast0` explicitly binds `p` at quantity `0` and explicitly performs
  equality induction;
- `relevantBad` presents an unrestricted proof and relies on the elaborator to
  insert a hidden transport.

It does not yet prove `cast0` sound. Explicitness tells the compiler which
semantics the programmer requested, but the requested operation is valid only
if Kappa guarantees that the endpoints share a compatible runtime
representation in the erased lane.

Nor should quantity monotonicity be lost. If an unrestricted proof is safe to
use as erased evidence, an explicit erased use of that proof should not fail
merely because the binder offered more capability. What may remain forbidden
is:

- an *implicit* downgrade performed by automatic transport insertion; or
- erasing evidence whose provenance belongs to a computational path system
  and whose transport is not representation-preserving.

The Spec currently has no explicit syntax or judgment distinguishing these two
reasons for rejection.

## 5. The actual soundness obligation

For an erased transport

```text
p : a = b
v : F a
----------------
transport p v : F b
```

to lower to the unchanged runtime payload, the compiler needs the following
property:

```text
RuntimeRep(F a) = RuntimeRep(F b)
```

This equality must cover more than byte width. It includes every
backend-observable part of the ABI:

- layout and alignment;
- calling convention;
- ownership and finalization convention;
- constructor/tag representation;
- bridge or foreign-boundary representation;
- runtime type metadata, if the operation preserves or observes it; and
- any effectful or computational action associated with path transport.

In a conventional erased intensional dependent type theory, this property is
usually an invariant of well-typed equality: erased indices do not change the
runtime carrier, and ordinary equality has no computational transport beyond
reflexivity. Kappa can adopt that invariant, but it must say so, especially
because the Spec also reserves proof-relevant and cubical extensions.

Without that invariant, a generic `cast0` is not portable. A future univalent
or computational path between types could transport by a nontrivial
equivalence rather than by the identity function. Erasing that path would lose
observable computation.

No-UIP alone settles neither side:

- declining to assume UIP does not automatically make ordinary erased
  transport unsafe; but
- the fact that equality has a single source constructor does not authorize a
  backend to erase every potentially proof-relevant transport.

The language needs a direct operational rule.

The obligation also constrains equality *producers*. An unresolved `expect`,
foreign declaration, trusted primitive, or extension cannot be allowed to
publish arbitrary erased evidence such as `Int = String` into a runnable
artifact and then rely on `cast0`: identity lowering would reinterpret an
`Int` payload as a `String`. Such a boundary must either certify
representation coherence, provide a proof-relevant lowering, remain outside
runnable portable artifacts, or be treated as an explicitly unsafe trust
boundary. Checking only the eliminator is too late if arbitrary equality has
already been admitted as safe erased evidence.

## 6. Coherent design options

### Option A: a normative representation-coherent erased lane

Define an erased-equality-induction judgment, conceptually:

```text
Γ ⊢ p : a = b @ erased
Γ ⊢ F respects erased equality representation
-------------------------------------------------
Γ ⊢ subst0 p : F a -> F b
```

For portable v1, the second premise may be a global theorem of well-formed
runtime types rather than a user-visible trait. The verifier records an
erasure justification, and KBackendIR receives the payload unchanged.

Evidence created by a future computational path feature is admitted to this
lane only when that feature proves the same representation property. Otherwise
it must use proof-relevant transport.

Consequences:

- `cast0` is accepted and lowers to the identity on `v`;
- `sym0` and `forcedRefl` remain accepted;
- automatic transport may use a proof that the source context already makes
  available only at quantity `0`, provided the erased-transport verifier
  accepts it;
- an explicitly erased use of an unrestricted proof may be accepted when its
  evidence source is eligible for this lane;
- `relevantBad` remains rejected because automatic insertion may not silently
  choose erased transport for an unrestricted proof; and
- computational paths retain their separate runtime semantics.

This option most closely matches the apparent intent of §17.1.3 and §31.2.

### Option B: restrict erased runtime transport

Revise §17.1.3 so that "the branch only refines types" is insufficient when
the refined branch returns a runtime value. Require one of:

- the whole result is checked at demand `0`;
- the equality type is known `RuntimeErased`;
- the proof is forced to `refl`;
- the transported family has a verified representation-preserving coercion;
  or
- a profile supplies a trusted lowering.

Consequences:

- `sym0` and `forcedRefl` remain positive;
- the fully generic `cast0` becomes a negative test, normally reporting
  `E_PROOF_RELEVANT_TRANSPORT_NOT_LOWERABLE` or a dedicated erased-transport
  diagnostic;
- safe indexed casts can still be expressed where the relevant premise is
  available; and
- the implementation has a smaller initial proof obligation.

This option is conservative and compatible with computational paths, but it
changes the plain reading of the existing §17.1.3 bullet and makes erased
dependent programming substantially less expressive.

### Option C: give every runtime type a uniform representation

A universal boxed representation could make arbitrary erased casts physically
safe. This would not by itself define computational path behavior, and it
would impose broad performance and foreign-interface costs. It is not a good
portable-language rule merely to solve this equality corner.

### Option D: make all runtime transport proof-relevant

The language could forbid erased equality induction whenever a runtime value
crosses the equality and require a computational lowering in every such case.
This is coherent, but it rejects the standard zero-cost indexed coercions that
quantity-`0` indices and §31.2 appear designed to support. It is not
recommended.

## 7. Recommended resolution

Adopt Option A for portable v1, with the following boundaries.

1. **Define erased equality induction explicitly.** A quantity-`0` proof may
   refine the static type of a runtime payload without inspecting the proof at
   runtime. The elaborated operation is an erased `pathInd`/`subst`, and the
   backend lowering is the identity on the payload.
2. **State the representation theorem.** Every ordinary equality evidence
   source admitted to erased induction must preserve the complete runtime
   representation and ABI of the transported family. KCore verification must
   reject erased transport when it cannot establish this invariant.
3. **Keep computational paths separate.** A future cubical, univalent, or
   trusted computational equality source is not automatically admissible to
   erased induction. Its feature profile must specify whether and when its
   evidence is representation-coherent; otherwise it uses proof-relevant
   transport.
4. **Do not let automatic insertion silently choose the erased lane.** For a
   runtime target and an unrestricted proof not known `RuntimeErased`,
   §16.1.8 should continue to reject unless the proof-relevant transport is
   lowerable. Explicit syntax or an explicit erased eliminator may request the
   erased lane. A proof whose binder is already quantity `0` is different: the
   source context has already committed that proof occurrence to erasure, so
   automatic insertion may use it after the same representation check.
5. **Preserve quantity monotonicity.** An unrestricted proof may be used in an
   explicitly erased occurrence when its equality evidence is eligible for
   erased induction. The compiler should not reject that explicit use merely
   because the binder has capability `ω` rather than `0`.
6. **Record the mode in KCore.** Erased and proof-relevant transports must be
   distinct after elaboration. Backend verification should never infer the
   mode from the source spelling `refl` or from optimization results.

This design gives a clear answer to the original question:

- matching a quantity-`0` proof does not magically make a runtime cast safe;
- it explicitly selects an erased induction mode whose representation safety
  the language guarantees and verifies;
- a quantity-`ω` proof is not less powerful, but an ordinary application does
  not explicitly select that erased mode; and
- hidden automatic transport therefore remains conservative.

If the project is unwilling to make the representation theorem part of Kappa
v1, it should adopt Option B instead and change `cast0` from a positive test to
a specified rejection. Leaving the current implication unstated is the least
desirable outcome.

## 8. Proposed Spec changes

### 8.1 Section 11.4.1

Add a third classification premise covering a proof occurrence explicitly
checked at demand `0` while the transported result remains runtime-relevant.
Define it as erased equality induction, not proof-relevant transport, and
attach the representation-coherence obligation.

Clarify that these facts are separate:

- the proof binder's quantity;
- whether the equality proof type satisfies `RuntimeErased`;
- the ambient demand of the eliminator result; and
- whether the transported runtime family is representation-coherent.

### 8.2 Section 16.1.8

Retain the current runtime restriction for automatic insertion. Add text that
the elaborator must not silently reinterpret an unrestricted proof as an
erased proof merely because an explicit erased induction using the same
logical equality would be legal.

Add a separate case for a proof made available only at quantity `0`. Under the
recommended design, automatic insertion may use it for a runtime-relevant
transport only when KCore can verify the erased lane's representation
obligation. Binder quantity alone selects the intended proof-use mode; it does
not discharge the representation check.

Also specify whether a future explicit erased-transport form may consume an
unrestricted proof at demand `0`. The recommendation is yes, subject to the
same evidence-provenance and representation checks.

### 8.3 Section 17.1.3

Replace "the branch is only refining types" with a testable rule. Suggested
direction:

> An equality branch that returns a runtime-relevant payload may refine that
> payload's type using an erased proof only when elaboration produces erased
> equality induction and KCore verifies representation coherence for the
> transported family. The branch must not inspect proof representation or
> select among proof identities at runtime.

Keep the forced-`refl` and erased-result cases as separate sufficient rules.

### 8.4 Section 31.2

Clarify that "type-directed coercion/refinement" means an identity operation on
the runtime payload only after the erased-transport justification has been
verified. Proof erasure alone is not the justification; the audit entry must
also identify why transport preserves representation.

### 8.5 KCore and KBackendIR verification

The serialized core form should distinguish at least:

```text
ErasedTransport(proof, motive, representationJustification)
ProofRelevantTransport(proof, motive, loweringRule)
```

The exact constructors are implementation-defined, but the distinction and
verification result must be stable enough for conformance, cache identity,
and backend safety. An erased transport reaching backend publication without
a valid justification must be rejected before KBackendIR is published.

## 9. Test disposition

### 9.1 `transport-runtime-relevance.kp`

Keep the fixture pending as a genuine implementation failure against the
current automatic-transport rules:

- `erasedOk` should pass because its equality proof is `RuntimeErased`;
- `demandZeroOk` should pass because the transported occurrence is under
  demand `0`; and
- `relevantBad` should be the fixture's sole rejection because its hidden
  runtime transport is neither erased by a stated premise nor lowerable.

The negative case should not be rewritten into an explicit match: doing so
would stop testing the important §16.1.8 rule.

### 9.2 `erased-equality-proof-match.kp`

Split the fixture conceptually into three obligations:

1. `sym0` is an uncontroversial positive erased-proof result.
2. `forcedRefl` is an uncontroversial positive runtime result because the
   equality is statically reflexive.
3. `cast0` is the decision test for this report.

Under the recommended Option A, all three remain positive and the fixture's
current `SPEC-CORRECT` status is justified by the new representation rule.
Under Option B, `cast0` must move to a separate negative fixture or receive a
`SPEC-ISSUE` status until a portable premise is added.

### 9.3 Additional tests needed after the decision

Add separate fixtures for:

- an explicit erased use of a proof supplied by an unrestricted binder;
- an automatic runtime transport using that same unrestricted proof, which
  remains rejected;
- a safe erased transport over an indexed family whose runtime carrier is
  visibly unchanged;
- a proof-relevant transport that reduces to `refl` before backend lowering;
- a proof-relevant transport that does not reduce and must report
  `E_PROOF_RELEVANT_TRANSPORT_NOT_LOWERABLE`; and
- if a computational path profile is enabled, one path admitted to erased
  transport and one path requiring its specified runtime operation.

These should be independent fixtures. Combining them under one error count
would make regressions in the positive exceptions hard to diagnose.

## 10. Open questions

1. Is representation coherence a theorem of all ordinary Kappa equality, or a
   checked property of a particular equality source and transported family?
2. Can a proof-relevant equality value always be consumed explicitly at
   demand `0`, or can computational-path provenance forbid that downgrade?
3. What source syntax requests erased induction when the available binder has
   quantity `ω`?
4. Does `RuntimeErased (a = b)` alone certify representation-preserving
   transport for every well-formed motive, or is an additional motive check
   required?
5. How is the representation justification serialized in KCore and audited
   before backend publication?
6. Should failure of the erased-lane premise use
   `E_PROOF_RELEVANT_TRANSPORT_NOT_LOWERABLE`, or should it receive a distinct
   diagnostic explaining that proof erasure does not establish runtime
   representation compatibility?
7. Will a future cubical/path extension reuse `(=)` or introduce a distinct
   path type? A distinct type would make the erased/proof-relevant boundary
   substantially easier to preserve.

## Conclusion

The two fixtures are not evidence that erased proofs are more powerful than
non-erased proofs. They expose three decisions that the current text partially
conflates:

- whether the programmer explicitly selected erased equality induction;
- whether automatic elaboration may make that selection silently; and
- whether the resulting change to a runtime value's static type is guaranteed
  to preserve representation.

The first can justify a different elaboration policy, but only the third makes
`cast0` sound. Kappa should state the representation-coherent erased lane
normatively, keep proof-relevant computational paths separate, and preserve
the conservative automatic-transport rule. Until that is done, the generic
`cast0` case is a specification issue rather than an adequately explained
conformance requirement.

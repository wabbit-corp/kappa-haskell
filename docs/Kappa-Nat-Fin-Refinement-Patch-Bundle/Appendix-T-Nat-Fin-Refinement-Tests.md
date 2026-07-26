# Appendix T Addendum: Nat, Arithmetic Proof Normalization, Fin, Refined, and Representation

Insert this as a new Appendix T subsection after the existing Appendix T example section.

These tests are written in the same conformance style as Appendix T: each item names a required portable outcome, and individual compiler suites may realize the item as an inline `.kp` test, a directory suite with KCore/KBackendIR dumps, or a pseudocode harness case when the checked artifact is not conveniently expressible in source. Human-readable diagnostics are not exact-match requirements unless a test says so. Humanity may yet escape regex-based spec conformance.

## T.12 Nat, arithmetic proof normalization, Fin, refinements, and representation conformance

### T.12.1 Logical Nat and ordinary computation

A conforming suite must check that:

* `Nat` exposes ordinary constructors `Nat.Zero` and `Nat.Succ` in the constructor namespace.
* Pattern matching on `Nat.Zero` and `Nat.Succ` is accepted in ordinary source.
* Structural recursion over `Nat` is accepted when the recursive call is on the predecessor.
* The standard source definitions `natAdd`, `natMultiply`, and `natCompare` are total-certified.
* Definitional conversion reduces `natAdd Zero n` to `n`.
* Definitional conversion reduces `natAdd (Succ m) n` to `Succ (natAdd m n)`.
* Definitional conversion reduces `natMultiply Zero n` to `Zero`.
* Definitional conversion reduces `natMultiply (Succ m) n` to `natAdd n (natMultiply m n)`.
* Definitional conversion does not require `natAdd n Zero` to reduce to `n` for neutral `n`.
* Definitional conversion does not require `natAdd n (Succ m)` to reduce to `Succ (natAdd n m)` for neutral `n` and `m`.
* Closed `Nat` arithmetic normalizes exactly for large values that exceed machine-word size.
* Overloaded `+` on canonical `Nat` resolves to the canonical `natAdd` semantic identity before arithmetic reification.
* `Nat` source semantics remain exact and unbounded even on backends with fixed-width host integer primitives.

Suggested inline shape:

```kappa
module t12_nat_basic

idLeft : (n : Nat) -> Vec (natAdd Nat.Zero n) A -> Vec n A
let idLeft n xs = xs

-- This one must check only through proof-directed transport or an explicit proof, not by ordinary conversion.
rightIdentityNeedsProof : (n : Nat) -> Vec (natAdd n Nat.Zero) A -> Vec n A
let rightIdentityNeedsProof n xs = transportNatIndex (natAddRightIdentity n) xs

--! assertNoErrors
```

### T.12.2 No-confusion and h-level derivation

A conforming suite must check that:

* `natSuccInjective` proves source equality of predecessors from equality of successors.
* `natZeroNotSucc` proves `Void` from a zero/successor equality.
* Same-constructor injectivity respects dependent telescope order for a GADT constructor.
* Distinct-constructor refutation is unavailable outside an opaque data representation unless exported through a checked theorem.
* A constructor result indexed by `m + n` remains reachable at demanded index `n + m` through explicit checked arithmetic bridge evidence rather than direct conversion.
* An arithmetic-refuted constructor-result bridge contributes `Empty` to source reachability.
* Failure to solve an unsupported constructor-result bridge remains `Unknown`, not `Empty`.
* KCore records propositionally compatible constructor bridges as explicit erased equality evidence, not as active conversion facts.
* `derive IsSet Nat` succeeds without a global UIP or `K` assumption.
* `derive Eq Nat` exposes `IsSet Nat` by ordinary supertrait projection.
* `derive IsSet` rejects an unsupported function field unless explicit `IsSet` evidence for that exact field type is available.
* Higher/path-constructor data is rejected by ordinary `derive IsSet` unless its extension supplies a checked h-level rule.
* Ordinary no-confusion does not infer point-constructor disjointness across path, higher, quotient, or boundary clauses without the extension certificate.

### T.12.3 Algebraic provider selection and determinism

A conforming suite must check that:

* Monoid identity simplification uses the selected coherent `AdditiveMonoid` evidence.
* Commutative normalization requires `CommutativeAdditiveMonoid`, not merely `AdditiveMonoid` or a suggestive trait name.
* `Semiring` normalization requires the conventional commutative-additive supertrait.
* A type with only `AdditivelyNoncommutativeSemiring` evidence does not receive commutative-addition normalization.
* Incompatible `AdditiveMonoid` evidence along `Semiring` supertrait paths is rejected by coherence checking.
* Unrelated total equality proofs are not scavenged into a normalization theory.
* Adding an unrelated import does not change provider selection, generated normal forms, proof/certificate bytes, or accepted status when the effective semantic environment is otherwise equivalent.
* Forged provider metadata, false member-role assignment, or a provider whose law projection has the wrong type is rejected during interface or certificate verification.

### T.12.4 Arithmetic solver and certificates

A conforming suite must check that:

* Required quantifier-free Presburger equalities and inequalities are decided over `Nat`, `Integer`, and `Int`.
* Checked `Nat` subtraction is reified only with its domain proof.
* Literal division and modulo congruences are decided for positive literal moduli.
* `min`, `max`, `clamp`, absolute value, and transparent arithmetic `if` expressions are handled by deterministic case splitting within the required fragment.
* Exact finite-domain proof search succeeds for verified domains of cardinality at most `256` when every enumerated predicate application normalizes under the test visibility and opacity environment.
* `?n + 1 = 4` may solve `?n := 3` when that is the unique principal solution.
* `?x + ?y = 4` does not guess a solution.
* A valid compact arithmetic certificate passes independent KCore verification.
* Changing an arithmetic certificate goal, assumption index, provider identity, domain version, or decisive payload makes verification fail with `E_KCORE_ARITHMETIC_CERTIFICATE_INVALID`.
* Certificate generation and canonical KCoreText round-trip are byte-stable for fixed semantic inputs.

Suggested harness assertions:

```text
--! assertArithmeticCertificatesValid
--! assertDiagnostic error E_KCORE_ARITHMETIC_CERTIFICATE_INVALID
```

### T.12.5 Fin

A conforming suite must check that:

* `Fin 0` has `SourceReachability = Empty`.
* `Fin 1` has `SourceReachability = Contractible`.
* Closed `Fin k` for `k >= 2` has `SourceReachability = Finite(k)`.
* Symbolic cardinality of `Fin n` is exactly `n`.
* `finZero`, `finSucc`, `finWeaken`, and `finLast` have their declared types.
* `finCases` covers every value of `Fin (n + 1)` exactly once up to equality.
* The zero case of `finInduction` is polymorphic in every positive bound, so it covers value zero in `Fin (k + 1)` for every `k`, not just `Fin 1`.
* `finInduction` is accepted as an ordinary proved eliminator.
* `finExt` proves equality from equality of underlying values.
* `Fin n` has a verified ordinal representation of cardinality `n`.
* `sizedArrayIndex` accepts `Fin n` and lowers through the private `sizedArrayIndexNat` primitive without retaining a runtime bound-proof field.
* A value of `Fin n` remains source-distinct from `Nat` even when KBackendIR assigns the same runtime representation.

Suggested harness assertions:

```text
--! assertInhabitance SourceReachability Empty for Fin 0
--! assertInhabitance SourceReachability Contractible for Fin 1
--! assertInhabitance SourceReachability Finite(5) for Fin 5
--! assertSymbolicCardinality n for Fin n
--! assertOrdinalRepresentation n for Fin n
--! assertRuntimeFieldAbsent finExample isLt
```

### T.12.6 Refined and proposition synthesis

A conforming suite must check that:

* An omitted proposition field is accepted only when checked `IsProp` evidence and an actual proof or checked certificate are synthesized for that fiber.
* `IsProp P` without an inhabitant of `P` does not construct `Refined A P`.
* `RuntimeErased P` without a proof of `P` does not construct the refinement.
* Two successfully synthesized proofs of an `IsProp` field do not cause incoherence merely because their proof terms differ.
* Safe proof evidence is preferred over unsafe/debug proof evidence when both are available.
* Quantity-`0` proof fields are absent from KBackendIR independently of how their proof was synthesized.
* Base-to-refinement insertion proves the predicate and inserts `refine`.
* Base-to-refinement insertion evaluates the source expression exactly once and does not duplicate, drop, or consume it beyond the original quantity/ownership demand.
* Refinement-to-base insertion projects `refinementValue` exactly once.
* Refinement widening proves the target predicate for the same stable projected base value and constructs the target once.
* The elaborator performs no unbounded chain search through `RefinementView` instances.
* `tryRefine` performs the explicit runtime decision for an arbitrary unproved value.
* `refinedExt` proves equality from equality of underlying values.
* `refinedIsSet` and generic `IsSet (Refined A P)` use stored per-value proposition evidence and do not require global function extensionality.
* Generic `Eq` and `Ord` for `Refined A P` compare the base value and remain proof-insensitive.

### T.12.7 Range membership by ordinary function

A conforming suite must check that:

* `contains (lo .. hi) x` elaborates through `Contains` and the selected canonical range evidence.
* Kappa v1 does not accept `x in lo..hi` as a special membership expression.
* A Type-valued refinement predicate writes Boolean membership explicitly as `(contains (lo .. hi) x) = True`; the bare Boolean is not silently coerced in an arbitrary lambda result type.
* Canonical inclusive Nat range membership reduces propositionally to `lo <= x && x <= hi`.
* Canonical exclusive Nat range membership reduces propositionally to `lo <= x && x < hi`.
* Recognition is unchanged by rebinding or importing the same semantic operations under different spellings.
* Literal construction inside a range is accepted when the predicate is proved.
* A reversed canonical numeric range is empty and has symbolic cardinality zero.
* A literal outside a closed range is rejected without a runtime check.
* Branch facts can establish range membership.
* Refinement widening proves range containment.
* An arbitrary runtime `Nat` requires explicit `tryRefine` rather than a silent dynamic check.

Suggested source sketch:

```kappa
type NatBetween (lo : Nat) (hi : Nat) : Type =
    Refined Nat (\x -> (contains (lo .. hi) x) = True)

three : NatBetween 2 30
let three = 3

--! assertNoErrors
```

Negative sketch:

```kappa
bad : NatBetween 2 30
let bad = 31

--! assertDiagnostic error E_TYPE_MISMATCH
```

### T.12.8 Symbolic cardinality and ordinal representation

A conforming suite must check that:

* Symbolic cardinality of inclusive exact range membership is `if lo <= hi then hi - lo + 1 else 0`.
* Exact sum and product cardinalities use unbounded arithmetic.
* An erased impossible proof field makes the enclosing constructor empty rather than a runtime singleton.
* `IsProp P` alone does not contribute an exact cardinality of one.
* `Fin n` has a verified ordinal representation of cardinality `n`.
* Finite enums, finite sums, finite products, and closed numeric ranges receive the required structural ordinal certificates.
* A valid KCoreText `representation-certificate` may bind an ordinary telescope, target an open family such as `Fin n` or a structural KCore type, record its canonical contextual `TypeNF` identity, and round-trip canonically.
* Corrupt rank/unrank round-trip evidence is rejected with `E_KCORE_REPRESENTATION_CERTIFICATE_INVALID`.
* Exact-natural certificates reject an extra retained successor field, a lazy recursive field, a wrong zero/successor mapping, or a failed structural round trip.
* Refinement certificates reject a second retained runtime field, a mismatched base projection, a failed round trip, or an erased-evidence observation.
* An ordinary handwritten `OrdinalRepresentation` instance without a compiler certificate does not change layout.
* A compiler-generated structural certificate does not silently publish a new global instance.
* Cardinality without ordinal evidence does not authorize dense encoding.

Suggested harness assertions:

```text
--! assertSymbolicCardinality (if lo <= hi then hi - lo + 1 else 0) for NatBetween lo hi
--! assertOrdinalRepresentation n for Fin n
--! assertExactNaturalRepresentation for Nat
--! assertRefinementRepresentation Nat for NatBetween 2 30
```

### T.12.9 Backend representation profiles

All runnable backends must pass tests showing that:

* `Nat` uses exact non-unary storage.
* Large `Nat` arithmetic remains exact.
* `Fin` proof fields are erased.
* Quantity-`0` refinement proof fields are erased.
* Source constructor and eliminator behavior is preserved after representation selection.
* A backend that cannot satisfy a mandatory representation contract rejects with `E_BACKEND_REQUIRED_REPRESENTATION_MISSING` rather than silently weakening semantics.

The `zig` profile, and any implementation-defined native profile claiming the same full internal-layout conformance class, additionally must pass tests showing that:

* the profile advertises `rt-compact-finite-ordinal`, `rt-packed-finite-fields`, and `rt-unboxed-refinement`;
* eligible certified finite values receive a compact documented ordinal class;
* arrays and fields use the smallest eligible documented packed lane when `rt-packed-finite-fields` applies; and
* KBackendIR records exact-natural, ordinal, refinement-certificate, and representation-class identities.

Managed JVM/CLR/Python profiles must pass tests showing that:

* host arbitrary-precision integers or hybrid exact-natural representations preserve exactness;
* nominal wrappers or host-word values may be preserved where the object model or boundary contracts require them;
* no minimum-byte finite layout is claimed unless the profile advertises the corresponding capability; and
* erased proof fields are removed and `Nat` is never lowered to a unary successor chain.

Suggested harness assertions:

```text
--! assertExactNaturalRepresentation for Nat
--! assertRuntimeFieldAbsent finExample isLt
--! assertRuntimeFieldAbsent refinedExample proof
--! assertRepresentationClass natExample ExactNatural
--! assertRepresentationClass finiteField FiniteOrdinal8
```

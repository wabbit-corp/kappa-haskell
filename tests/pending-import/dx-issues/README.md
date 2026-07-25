# Developer-experience regression tests

These staged fixtures encode common source-reading expectations or the minimum
diagnostic quality needed when Kappa deliberately chooses a less conventional
surface rule. They are not assertions that the current `Spec.md` already
requires every proposed behavior.

The parser cases come from `docs/WORKER_DISCOVERED_ISSUES.md` and reproduce
real edits that produced remote or misleading diagnostics. The token-boundary
and floating-equality cases cover language-design footguns already identified
in `docs/notes/KNOWN_SPEC_ISSUES.md`. The declaration-head keyword, polymorphic
union specialization, and custom prefix-minus cases come from the subsequent
whole-spec missed-coverage audit.

## Validation snapshot

Run independently against the existing working-tree compiler binary on
2026-07-22 (no rebuild): **0 pass / 9 fail / 0 unsupported / 0 harness-error**.
The parser failures reproduce the expected orphaned-`else`, declaration-head
soft-keyword, soft-`effect`, remote operator-continuation, and `]>`
token-boundary problems. The type-system probes additionally show that a
polymorphic union specialization silently acquires duplicate members and that a
local prefix-minus binding is bypassed in favor of hard-wired integer negation.
Run mode also silently accepts a valid module with no entrypoint instead of
emitting its registered `E_NO_MAIN` diagnostic.

The float case otherwise runs with the specified raw-bit/numeric results and
fails only because no advisory warning is emitted.

## 2026-07-23 additions (round 3)

~60 new probes from the probe-first DX audit lanes: classic beginner-mistake
diagnostics (`=` vs `==`, missing `do`/`then`/`else`, forgotten `pure`, arity
short-falls), name-resolution fix-it quality (§3.1.7 repair ranking), cascade
suppression (§3.1.14A), warning hygiene (§3.1.12: unused/shadowed/unreachable),
prelude ergonomics beyond the §28.2 MUSTs, layout edges (CRLF, BOM, tabs),
runtime common-sense (division by zero, Double printing, exit codes), and
same-mistake-different-route diagnostic consistency. Each file's header states
whether the expectation is spec-required or a DX proposal; every file ends with
a `-- STATUS(a0497523): ...` line recording actual behavior.

Validation snapshot 2026-07-23 (clean `a0497523` binary, per-file runs):
**3 pass / 65 fail** across the 68 staged dx units — the fails are the point:
each pins an expectation the current compiler does not meet.

2026-07-23 promotions: the BOM, CRLF-multiline, comprehension-splice, and
dead-code-after-return probes were promoted to spec-required behavior (Spec
SS5 source text, SS5.4 line terminators, SS6.3.3 content normalization,
SS18.3.1 comprehension boundary, SS18.2.2 + SS3.2.21 W_DO_ITEM_UNREACHABLE)
and moved to ../spec-coverage/ (lexical/, literals/, do-blocks/).

2026-07-23 promotions (second batch): var-never-read lint, record-field
rename fix, radix token boundary, qualifier suggestion ranking, leading-
operator and hanging-else continuations, named-arg cascade suppression,
instance-head name resolution, and gensym hygiene were promoted to
spec-required behavior (Spec SS3.1.7, SS3.1.11, SS3.2.3, SS3.2.20, SS5.4,
SS6.1.1, SS14.3) and moved to ../spec-coverage/.

## 2026-07-24 additions — type-level operations batch

20 probes from the type-level-computation audit (triggered by the
ATS-datasort "symbolic index identities are not definitional" comment):
the prelude-Nat symbolic dead end (identities neither definitional nor
provable — no induction principle, no Eq.eqSound/eqComplete members, law
members assertion-backed), runtime-fact-to-index bridges that never fire
(== branch evidence, literal-pattern refinement, the Spec 11.4.2 dependent
boolean field), GADT-over-primitive-Nat construction-without-elimination,
the TypeLevel-vs-Nat solver asymmetry, index-mismatch rendering leaking
internal Core spellings, literal-defaulting footguns, an erased-motive
rejection, an implicit-ambiguous cascade, TWO compiler crashes (uncaught
ErrorCall on universalized-application equality; eval de Bruijn/stack
overflow on a malformed vector file), and one SOUNDNESS hole (`witness`
solves ANY implicit goal whose type is still a metavariable — `a = b`
accepted from an empty context).

Validation snapshot 2026-07-24 (clean `a0497523` binary): all 20 fail or
crash as recorded per-file; each ends with a `-- STATUS(a0497523): ...`
line. The same audit added 15 PASSING conformance pins under
`tests/conformance/spec-coverage/` (definitional-reduction boundary,
prove-then-transport chains, flow-bridge discharges, the PNat vector
journey) and 5 rerouted compiler-gap pins under
`../spec-coverage/` (TypeLevel solver identities not reachable from
ordinary source; bool-match comparison bridge).

2026-07-24 promotions: float extreme-rounding warnings, opaque-alias
instance-head identity, prefix-minus operator resolution, data-header EOF
recovery quality, context-sensitive ']>' lexing, soft-keyword declaration
heads, and the Eq eqSound/eqComplete member gap were promoted (Spec SS6.1.3,
SS14.3.2, SS6.1.4, SS3.1.14A, SS5.5.1, SS5.2; eq-eqsound needed no spec
change) and moved to ../spec-coverage/.

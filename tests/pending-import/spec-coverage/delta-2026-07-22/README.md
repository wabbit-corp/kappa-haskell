# Spec delta coverage — 2026-07-22

These staged tests cover normative combinations added or materially changed after
the 2026-07-19 whole-spec campaign. They intentionally remain outside
`tests/conformance` while the universe/observation implementation is changing.

The fixtures have since been distributed into the parent directory's semantic
area folders; this file remains here as the campaign report.

Coverage in this campaign:

- §3.1.13 and §3.2.3: explanation pages for the new universe, observation,
  generalization, schema-certificate, and KCoreText diagnostics;
- §11.1.1, §11.1.2.3B, §12.1.1, and §30.2.0: first-class levels and the
  independence of observation mode, quantity, and borrowed access;
- §13.2.5 and §17.1.7A: parametric witnesses through dependent record updates
  and record patterns;
- §14.3.1A and §21.2: parametric witnesses through generated syntax, including
  the corresponding ordinary-promotion rejection;
- §14.3 (universe-schema cumulativity): schema lifts must not manufacture
  instance-head matches;
- §10.4.3 and §11.1.2.3A.2: source-level mutual nominal role inference reaches
  a fixed point; and
- §12.1.1: one-way observation subsumption is limited to the outer Pi spine.

Each case combines the target rule with at least one other feature (macros,
dependent records, patterns, traits, opaque level functions, mutual data, or
borrowed binders) so the test exercises preservation across a real elaboration
boundary rather than only the isolated syntax.

## Validation snapshot

Run independently against the existing working-tree compiler binary on
2026-07-22 (no rebuild): **8 pass / 4 fail / 0 unsupported / 0 harness-error**.

The four failures are intentional staged gaps:

- `generalization-parametric-escape-payload.kp`: the diagnostic has no required
  structured payload;
- `record-update-parametric-witness-positive.kp`: finalized Core fails the
  observation-dependency analysis after the dependent update/pattern/repack;
- `typelevel-pattern-opaque-index-positive.kp`: the record-pattern equality is
  not used to transport the erased bound proof and indexed argument; and
- `universe-variance-diagnostic-payload.kp`: the role diagnostic omits required
  nominal/parameter/role payload fields.

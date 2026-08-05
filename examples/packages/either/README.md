# Either for Kappa

A small support package providing the neutral `Either a b` coproduct and its
`Left`/`Right` constructors. Kappa's prelude `Result e a` remains the right
choice for failure/success APIs; this type is for branch-symmetric code.

It lives separately so foundational ports can share one nominal coproduct while
the missing canonical prelude type remains pinned as a DX issue.

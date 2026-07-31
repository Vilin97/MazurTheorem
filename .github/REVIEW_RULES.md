# Review rules

Review is adversarial and evidence-based. A green kernel check is necessary,
but it does not establish that the statement says the intended mathematics,
that an interface will compose, or that progress has been credited honestly.

Reviewers should return one of three verdicts:

- **block** — unsound, mis-formalized, unlicensed, misleading, or outside the
  repository trust policy;
- **changes requested** — viable, but the proof, API, evidence, or
  documentation needs concrete revision;
- **approve** — mathematically faithful, kernel-clean, maintainable, and
  integrated at the level claimed.

## Required review questions

1. **Mathematical fidelity.** Does the Lean statement match the cited result,
   including fields, quantifiers, nondegeneracy conditions, exact orders, and
   cusp or smoothness hypotheses? Try to construct trivial witnesses or
   degenerate counterexamples.
2. **Kernel trust.** Are all declarations placeholder-free outside registered
   challenge bodies? Does the axiom audit remain within `propext`,
   `Quot.sound`, and `Classical.choice`?
3. **Dependency honesty.** Are imports and pins exact? Is unfinished upstream
   work being treated only as design prior art rather than as a proved
   dependency?
4. **API design.** Is the declaration stated at the right level of generality
   and in the right namespace? Can the named consumer use it without exposing
   private proof machinery?
5. **Reuse and duplication.** Was Mathlib, Tau Ceti, Lean Pool, and the audited
   prior-art inventory checked first? If a local result belongs upstream, is
   the adapter intentionally thin?
6. **Proof quality.** Are the main reductions legible and stable? Do large
   certificates have a reproducible mathematical origin and manageable
   elaboration cost?
7. **Provenance.** Are authors, source commits, licenses, and AI/human
   provenance recorded accurately?
8. **Progress accounting.** Does the registered consumer actually compile?
   Does the lifecycle change follow the public scoring method without
   changing weights opportunistically?

Reviewers should name exact declarations and counterexamples, not merely give
style impressions. If a result is correct but the interface is premature,
request the interface change before more proof volume accumulates behind it.

Large foundational interfaces should receive two approvals, including one
review focused on downstream usability. A roadmap-weight change is reviewed
separately from the proof that motivated it.

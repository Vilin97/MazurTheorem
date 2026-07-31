# Solution review rules

The Lean kernel decides whether a term proves the registered proposition.
Review decides whether the contribution is the right maintainable proof for
this programme.

A solution must:

- prove the exact registered declaration without weakening or restating it;
- live in checked implementation or the declared upstream package, never
  behind an import of the open challenge;
- use no placeholders, custom axioms, unsafe escape hatches, linter waivers,
  or proof-strengthening options;
- compile the named downstream consumer;
- preserve exact dependency pins unless the pull request is explicitly a pin
  migration;
- record mathematical sources, proof authorship, generated-certificate
  provenance, and any upstream contribution;
- pass the source, warning, style, linter, and transitive axiom checks.

Reviewers should still test for a vacuous bridge, accidental stronger
hypotheses, private declarations leaking into the public API, duplicated
upstream work, and avoidable elaboration or memory costs. A very large proof
may be returned for semantic splitting even when it compiles.

Once accepted, replace the registered challenge body only with a thin bridge
to the public implementation theorem. The roadmap node receives full credit
only after its registered consumer compiles.

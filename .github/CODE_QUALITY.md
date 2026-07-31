# Code quality policy

This repository combines a checked Lean development, open challenge
contracts, attributed ports, generated arithmetic certificates, and public
coordination artifacts. The trust boundary must stay visible.

## Source classes

- `MazurTorsion/`, `EllipticCurves/`, and their root modules are checked
  implementation. They must be placeholder-free.
- `Challenge/` and `upstream/tauceti/MazurTauCetiChallenge/` contain the
  registered contracts. An unsolved open declaration may use exactly one
  whole-body `:= sorry`; solved contracts are checked bridges, and no
  supporting declaration may be open.
- `archive/drafts/` is historical text. It is excluded from Lake libraries,
  proof claims, documentation extraction, and progress credit.

Checked implementation must not contain `sorry`, `admit`, custom `axiom`
declarations, `native_decide`, `unsafe`, `partial`, linter suppressions, or
local option changes that weaken checking. A proof must not import a
challenge module.

## Lean files

Every file starts with the copyright, Apache-2.0 license, and complete author
header, followed by imports and a module docstring. Preserve upstream author
headers and record every port in `THIRD_PARTY_NOTICES.md` and
`docs/PRIOR_ART.md`.

Use the narrowest practical imports. Public declarations should:

- use full, descriptive names in the owning namespace;
- state the stable mathematical interface, not an accidental proof encoding;
- expose the hypotheses actually consumed;
- include a docstring explaining the mathematical role;
- have a named downstream consumer before receiving integrated credit.

Large certificate proofs are acceptable when the mathematics is inherently
computational. Split them at semantic boundaries, keep expensive terms out of
public theorem types, and document the certificate source and checking
strategy. Generated volume is not evidence of progress.

## Kernel and build discipline

Completed declarations may depend only on `propext`, `Quot.sound`, and
`Classical.choice`. CI imports both checked library roots and audits transitive
axiom dependencies; a source-text scan is not a substitute for this audit.

Build the smallest affected module locally with one Lean worker. Full cold
builds and documentation builds belong in CI because the imported baseline is
large. A pull request must compile both the changed declaration and its named
consumer without warnings.

Do not weaken checks to accommodate a contribution. Fix the source.

## Coordination artifacts

`coordination/program.json` is the source of truth for weights, dependencies,
readiness, and challenge metadata. The site copy must be generated from it and
remain byte-identical. A roadmap node earns completion credit according to
`docs/PROGRESS_METHOD.md`, never from issue closure, line count, or an
unconsumed proof.

Changes to mathematical scope, node weights, dependency pins, or public
interfaces require an explicit explanation in the pull request. Dependency
pin updates should not be mixed with proof work.

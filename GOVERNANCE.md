# Governance

Mazur Theorem is a maintainer-led, public research project.

## Roles

- **Maintainers** own releases, dependency pins, roadmap weights, security,
  and final integration.
- **Track stewards** review the mathematical direction and API of a roadmap
  stage.
- **Contributors** own a bounded claim or research work package.

Maintainers may delegate review without delegating the responsibility to keep
the global theorem statement honest.

## Decisions

Routine proof and documentation decisions use normal pull-request review.
The following require a public design issue and explicit maintainer approval:

- changing the target theorem;
- changing roadmap weights or completion rules;
- adding a foundational dependency;
- publishing a new interface work package;
- changing the axiom or source-quality policy;
- declaring a research node complete.

Where reviewers disagree, maintainers record the decision and reasoning in
the issue. Mathematical correctness is never decided by vote: the Lean
kernel, the axiom audit, and the cited source remain mandatory.

## Roadmap integrity

`coordination/program.json` is the canonical project ledger. Node identifiers
are permanent. Weight changes are exceptional and must not be used to create
the appearance of progress. A statement alone earns zero completion credit.

Claims are leases, not ownership. A normal claim lasts 14 days and needs a
weekly progress note. Research nodes may support parallel teams. Stale claims
can be released so the project does not deadlock.

## Releases

The default branch is always expected to build. Milestones are cut only from
an exact commit whose core proof, registered challenge policy, site, and
documentation checks are green.

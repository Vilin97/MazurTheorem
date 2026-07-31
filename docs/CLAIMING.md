# Claiming work

## Claimable challenges

Every roadmap node with `"challenge": {"claimable": true}` has a compiled
contract. Status `"open"` means it is ready for an ordinary claim; status
`"research_open"` means only a nonexclusive research intention is available.
Each card provides an exact import, declaration, destination module, consumer,
dependencies, and acceptance conditions.

Open the repository's “Claim a work package” issue form. A normal claim:

- lasts 14 days;
- needs a public progress note at least once every 7 days;
- may be extended when there is concrete progress;
- can be released at any time without stigma.

Maintainers may release a silent claim so other contributors are not blocked.

## Research nodes

`research_open` nodes can have multiple teams. A research intention reserves
no namespace and does not prevent independent approaches. Use the “Register a
research approach” form, and share negative results, interface discoveries,
and source references early.

## Interface nodes

For `draft_interface` or `nouns_missing`, open a design issue first. Include:

- the consumer theorem that motivates the API;
- proposed exact Lean signatures;
- upstream destination and dependency pin;
- sanity examples;
- what the interface deliberately does not promise.

Two reviewers should approve large foundational interfaces before proof-heavy
implementation begins.

## Closing a claim

A claim closes only when the PR compiles the registered declaration and its
named consumer, passes the axiom/source gates, records provenance, and updates
the lifecycle without changing the task's mathematical meaning.

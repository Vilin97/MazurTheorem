# Challenge review rules

A challenge is a public mathematical contract, not a placeholder-shaped wish.
Once claimed, its mathematical statement is immutable except to repair a
demonstrable error.

Approve a new challenge only when all of the following hold:

1. The declaration compiles at its recorded Lean and dependency pins.
2. The informal statement faithfully describes the Lean proposition.
3. Any cited known result is stated in the form supported by its source.
4. The proposition is nonvacuous: its hypotheses are jointly realizable, its
   conclusion is not already definitional, and no irrelevant parameter makes
   it trivially true.
5. The imports are the narrowest practical imports and introduce no unfinished
   assumptions.
6. The registered declaration contains exactly one whole-body `:= sorry`;
   every definition and supporting lemma is closed.
7. A named consumer or explicit integration adapter explains how a solution
   advances the theorem. A useful upstream interface challenge may instead
   name a concrete acceptance consumer in its own pinned package.
8. The proposed route and line estimate are plausible enough to distinguish a
   bounded challenge from an undecomposed research programme.
9. Required definitions already exist. If the nouns or their API are still
   under design, register an interface or research node instead.
10. Provenance, license, source, risk, and coordination mode are explicit.

For a `research_open` challenge, parallel approaches must remain welcome and
no issue claim may reserve the whole problem. For an ordinary claimable
challenge, the fourteen-day lease and heartbeat policy applies.

Publishing or solving a statement does not itself justify changing roadmap
weights. Completion credit is awarded only by the gates in
`docs/PROGRESS_METHOD.md`.

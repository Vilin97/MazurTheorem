# Security policy

This repository contains proof source and a public, read-only coordination
site. The site has no authentication, user data, uploads, or persistent
application state. The relevant security risks are compromised build
dependencies, workflow injection, deployed-site vulnerabilities, and unsound
verification claims.

Please report vulnerabilities privately with
[GitHub's security advisory form](https://github.com/Vilin97/MazurTheorem/security/advisories/new).
Do not open a public issue before maintainers have had a chance to assess it.

Reports about a possible logical gap should include the exact commit,
declaration, unexpected axiom or elaboration behavior, and a minimal
reproducer. We will credit reporters who want attribution.

Only the latest commit on `main` is supported.

CI blocks high-severity advisories in deployed site dependencies. Development
tooling is not shipped to production; its audit findings are reviewed
separately so a linter-only transitive advisory cannot be mistaken for a
runtime exposure.

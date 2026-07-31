# Mazur Theorem coordination site

The public dashboard turns `../coordination/program.json` into a readable,
filterable view of the formalization programme.

## Local development

Requires Node.js 22.13 or newer.

```bash
npm install
npm run dev
```

The production-compatible checks are:

```bash
npm run lint
npm test
```

`npm test` builds the vinext/Cloudflare Worker bundle and checks the
server-rendered page for the programme title, progress ledger, roadmap,
challenge boundaries, and absence of starter-preview metadata.

## Data contract

The dashboard imports `coordination/program.json` at build time. Edit the
canonical ledger there; do not hand-edit progress numbers in the site.

The site intentionally has no database, authentication, or runtime mutation.
Claims and discussion happen in GitHub issues, while the checked JSON ledger
remains the source of truth.

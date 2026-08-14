import assert from "node:assert/strict";
import { access, readFile } from "node:fs/promises";
import test from "node:test";

const siteRoot = new URL("../", import.meta.url);
const leanNameSegment = String.raw`[_\p{L}][\p{L}\p{N}_']*`;
const qualifiedLeanNamePattern = new RegExp(
  `^(?:${leanNameSegment})(?:\\.(?:${leanNameSegment}))+$`,
  "u",
);

async function render() {
  const workerUrl = new URL("../dist/server/index.js", import.meta.url);
  workerUrl.searchParams.set("test", `${process.pid}-${Date.now()}`);
  const { default: worker } = await import(workerUrl.href);
  return worker.fetch(
    new Request("http://localhost/", {
      headers: { accept: "text/html" },
    }),
    {
      ASSETS: {
        fetch: async () => new Response("Not found", { status: 404 }),
      },
    },
    {
      waitUntil() {},
      passThroughOnException() {},
    },
  );
}

test("server-renders the coordination dashboard", async () => {
  const programme = JSON.parse(
    await readFile(
      new URL("../../coordination/program.json", import.meta.url),
      "utf8",
    ),
  );
  const challengeNodes = programme.nodes.filter(
    (node) => node.challenge?.claimable === true,
  );
  const ordinaryChallengeCount = challengeNodes.filter(
    (node) => node.status === "open",
  ).length;
  const researchChallengeCount = challengeNodes.filter(
    (node) => node.status === "research_open",
  ).length;
  const pausedChallengeCount = programme.nodes.filter(
    (node) => node.status === "paused" && node.challenge,
  ).length;
  const integratedPercent = programme.progress.percent;

  const response = await render();
  assert.equal(response.status, 200);
  assert.match(response.headers.get("content-type") ?? "", /^text\/html\b/i);

  const html = await response.text();
  assert.match(
    html,
    /<title>Mazur Theorem · Formalization Programme<\/title>/i,
  );
  assert.match(html, /Mazur’s classification/);
  assert.match(html, /built on canonical objects/);
  assert.match(html, /rationalTorsion_hasMazurClassification/);
  assert.match(html, /DegreeOneFormalImmersionWitness/);
  assert.match(
    html,
    /One theorem spine. Only startable foundation lanes are active/,
  );
  assert.equal(
    (html.match(/class="lane-card"/g) ?? []).length,
    programme.execution.active_lanes.length,
  );
  assert.match(html, /Evidence-weighted ledger/);
  assert.match(html, new RegExp(`>${integratedPercent}%<\\/span>`));
  assert.match(html, /Ecosystem-ready estimate/);
  assert.match(
    html,
    new RegExp(
      `>${programme.progress.ecosystem_ready_estimate_percent}(?:<!-- -->)?%<\\/strong>`,
    ),
  );
  assert.match(html, /The weighted roadmap/);
  assert.equal((html.match(/class="stage-card"/g) ?? []).length, 6);
  assert.equal((html.match(/aria-controls="stage-details-/g) ?? []).length, 6);
  assert.equal((html.match(/id="stage-details-/g) ?? []).length, 6);
  assert.match(html, /aria-expanded="true"/);
  assert.match(html, /What this stage must define and prove/);
  assert.match(html, /All (?:<!-- -->)?1(?:<!-- -->)? dependency nodes?/);
  assert.match(html, /Interactive dependency graph/);
  assert.match(html, /Every node, edge, and hand-off/);
  assert.match(html, new RegExp(`All ${programme.nodes.length} nodes`));
  assert.match(
    html,
    /aria-label="Focus graph on stage 3: Shared algebraic geometry and isogenies"/,
  );
  assert.match(html, /Mazur theorem dependency graph/);
  assert.match(html, /Browse the graph as a dependency list/);
  assert.match(html, /Definitions, theorems, and API surface/);
  assert.match(html, /Lean acceptance boundary/);
  assert.match(html, /MT-O25-EXCLUDE/);
  assert.match(html, /MT-X13-NONCUSP/);
  assert.match(html, /MT-TC-A1-ORDER-SUPPORT/);
  assert.match(html, /Claim this challenge/);
  assert.match(html, /Register an approach/);
  assert.match(html, /Open contracts/);
  assert.match(
    html,
    new RegExp(
      `${ordinaryChallengeCount}(?:<!-- -->)? ordinary claims worth(?:<!-- -->)? `,
    ),
  );
  assert.match(
    html,
    new RegExp(
      `${programme.progress.ordinary_claimable_points}(?:<!-- -->)? points`,
    ),
  );
  assert.match(
    html,
    new RegExp(
      `${researchChallengeCount}(?:<!-- -->)? nonexclusive research intentions worth`,
    ),
  );
  assert.match(
    html,
    new RegExp(
      `${programme.progress.research_open_points}(?:<!-- -->)? points`,
    ),
  );
  assert.match(html, /template=claim\.yml(?:&amp;|&)title=%5BClaim%5D/);
  assert.match(
    html,
    /template=research-intention\.yml(?:&amp;|&)title=%5BResearch%5D/,
  );
  assert.match(html, /nonexclusive research intentions worth/);
  assert.match(html, /Deliberately paused/);
  assert.equal(
    (html.match(/class="paused-card"/g) ?? []).length,
    pausedChallengeCount,
  );
  assert.match(html, /speculative proof volume stopped/);
  assert.match(html, /Work-package allocations only divide/);
  assert.match(html, /How progress is scored/);
  assert.match(
    html,
    /https:\/\/mazur-theorem-formalization\.vilin402100\.chatgpt\.site\/og-v2\.png/,
  );
  assert.match(html, new RegExp(`${integratedPercent}% integrated`));
  assert.doesNotMatch(html, /codex-preview/);
  assert.doesNotMatch(html, /Your site is taking shape/);
  assert.doesNotMatch(html, /react-loading-skeleton/);
});

test("starter preview and generic assets are removed", async () => {
  await assert.rejects(access(new URL("app/_sites-preview", siteRoot)));
  await assert.rejects(access(new URL("app/chatgpt-auth.ts", siteRoot)));
  await assert.rejects(access(new URL("public/file.svg", siteRoot)));
  await assert.rejects(access(new URL("public/globe.svg", siteRoot)));
  await assert.rejects(access(new URL("public/window.svg", siteRoot)));
});

test("the site data is byte-identical to the canonical ledger", async () => {
  const [canonical, generated] = await Promise.all([
    readFile(new URL("../../coordination/program.json", import.meta.url)),
    readFile(new URL("../generated/program.json", import.meta.url)),
  ]);
  assert.deepEqual(generated, canonical);
});

test("qualified Lean names support Unicode letters but not numeric starts", () => {
  assert.match(
    "ModularCurves.pullback_δ_unit_tensorSection",
    qualifiedLeanNamePattern,
  );
  assert.doesNotMatch("ModularCurves.₁bad", qualifiedLeanNamePattern);
  assert.doesNotMatch("ModularCurves.²bad", qualifiedLeanNamePattern);
  assert.doesNotMatch("ModularCurves.Ⅻbad", qualifiedLeanNamePattern);
});

test("every roadmap node exposes concrete artifacts or an exact challenge", async () => {
  const source = await readFile(
    new URL("../../coordination/program.json", import.meta.url),
    "utf8",
  );
  const programme = JSON.parse(source);
  for (const node of programme.nodes) {
    const hasArtifacts =
      Array.isArray(node.artifacts) && node.artifacts.length > 0;
    assert.ok(
      hasArtifacts || node.challenge?.declaration,
      `${node.id} has neither artifacts nor an exact challenge`,
    );
    for (const artifact of node.artifacts ?? []) {
      assert.match(
        artifact.name,
        qualifiedLeanNamePattern,
        `${node.id} has a non-qualified artifact name`,
      );
      assert.ok(
        ["contract", "integrated", "proposed"].includes(artifact.state),
        `${node.id} has an invalid artifact state`,
      );
    }
    for (const entry of node.external_reuse ?? []) {
      assert.equal(typeof entry.source, "string", `${node.id} source`);
      assert.equal(typeof entry.status, "string", `${node.id} status`);
      assert.equal(typeof entry.summary, "string", `${node.id} summary`);
      assert.equal(typeof entry.boundary, "string", `${node.id} boundary`);
      assert.equal(
        typeof entry.estimated_node_savings_percent?.min,
        "number",
        `${node.id} minimum node-savings estimate`,
      );
      assert.equal(
        typeof entry.estimated_node_savings_percent?.max,
        "number",
        `${node.id} maximum node-savings estimate`,
      );
      assert.ok(
        entry.estimated_node_savings_percent.min <=
          entry.estimated_node_savings_percent.max,
        `${node.id} has an inverted node-savings range`,
      );
      assert.ok(
        Array.isArray(entry.declarations),
        `${node.id} declarations must be an array`,
      );
      for (const declaration of entry.declarations) {
        assert.equal(
          typeof declaration.name,
          "string",
          `${node.id} declaration name`,
        );
        assert.match(
          declaration.url,
          /^https:\/\//,
          `${node.id} declaration URL`,
        );
      }
    }
  }
});

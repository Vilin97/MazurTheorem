import assert from "node:assert/strict";
import { access, readFile } from "node:fs/promises";
import test from "node:test";

const siteRoot = new URL("../", import.meta.url);

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
  const response = await render();
  assert.equal(response.status, 200);
  assert.match(response.headers.get("content-type") ?? "", /^text\/html\b/i);

  const html = await response.text();
  assert.match(html, /<title>Mazur Theorem · Formalization Programme<\/title>/i);
  assert.match(html, /Mazur’s theorem/);
  assert.match(html, /Evidence-weighted ledger/);
  assert.match(html, />5%<\/span>/);
  assert.match(html, /Ecosystem-ready estimate/);
  assert.match(html, />12(?:<!-- -->)?%<\/strong>/);
  assert.match(html, /The weighted roadmap/);
  assert.match(html, /Lean acceptance boundary/);
  assert.match(html, /no_rational_point_of_order_twentyFive/);
  assert.match(html, /addOrderOf P ≠ 25 := sorry/);
  assert.match(html, /xOneThirteen_no_noncuspidal_point/);
  assert.match(html, /orderThirteenHyperellipticPolynomial x/);
  assert.match(html, /MT-TC-A1-ORDER-SUPPORT/);
  assert.match(html, /Claim this challenge/);
  assert.match(html, /Register an approach/);
  assert.match(html, /Open contracts/);
  assert.match(html, /8(?:<!-- -->)? boundaries/);
  assert.match(html, /113(?:<!-- -->)? pts/);
  assert.match(html, /4(?:<!-- -->)? ordinary claims worth(?:<!-- -->)? /);
  assert.match(html, /39(?:<!-- -->)? points/);
  assert.match(html, /4(?:<!-- -->)? nonexclusive research intentions worth/);
  assert.match(html, /74(?:<!-- -->)? points/);
  assert.match(html, /template=claim\.yml(?:&amp;|&)title=%5BClaim%5D/);
  assert.match(
    html,
    /template=research-intention\.yml(?:&amp;|&)title=%5BResearch%5D/,
  );
  assert.match(html, /nonexclusive research intentions worth/);
  assert.match(html, /How progress is scored/);
  assert.match(
    html,
    /https:\/\/mazur-theorem-formalization\.vilin402100\.chatgpt\.site\/og\.png/,
  );
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

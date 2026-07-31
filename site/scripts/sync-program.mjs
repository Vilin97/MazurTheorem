import { mkdir, readFile, writeFile } from "node:fs/promises";

const canonicalUrl = new URL("../../coordination/program.json", import.meta.url);
const generatedUrl = new URL("../generated/program.json", import.meta.url);
const checkOnly = process.argv.includes("--check");

const canonical = await readFile(canonicalUrl);

try {
  const programme = JSON.parse(canonical.toString("utf8"));
  if (
    !programme ||
    programme.schema_version === undefined ||
    !Array.isArray(programme.stages) ||
    !Array.isArray(programme.nodes)
  ) {
    throw new Error("missing schema_version, stages, or nodes");
  }
} catch (error) {
  const detail = error instanceof Error ? error.message : String(error);
  throw new Error(`Invalid coordination/program.json: ${detail}`);
}

if (checkOnly) {
  let generated;
  try {
    generated = await readFile(generatedUrl);
  } catch {
    throw new Error(
      "site/generated/program.json is missing; run npm run programme:sync",
    );
  }

  if (!canonical.equals(generated)) {
    throw new Error(
      "site/generated/program.json is stale; run npm run programme:sync",
    );
  }
} else {
  await mkdir(new URL("../generated/", import.meta.url), { recursive: true });
  await writeFile(generatedUrl, canonical);
  process.stdout.write("Synced coordination/program.json into site/generated.\n");
}

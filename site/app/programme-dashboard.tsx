"use client";

import { useMemo, useState } from "react";
import type {
  Challenge,
  Programme,
  ProgrammeNode,
  ProgrammeStage,
} from "./programme-types";

const GITHUB = "https://github.com/Vilin97/MazurTheorem";
const DOCUMENTATION = "https://vilin97.github.io/MazurTheorem";

function words(value: string) {
  return value
    .replace(/[_-]+/g, " ")
    .replace(/\b\w/g, (letter) => letter.toUpperCase());
}

function backends(node: ProgrammeNode) {
  return Array.isArray(node.backend) ? node.backend : [node.backend];
}

function statusTone(status: string) {
  const value = status.toLowerCase();
  if (value.includes("complete") || value.includes("done")) return "complete";
  if (value.includes("progress") || value.includes("active")) return "active";
  if (value.includes("open") || value.includes("claim")) return "open";
  if (value.includes("block")) return "blocked";
  return "planned";
}

function riskTone(risk: string) {
  const value = risk.toLowerCase();
  if (value === "high" || value.includes("extreme")) return "high";
  if (value === "medium") return "medium";
  return "low";
}

function percentage(value: number) {
  return `${Math.max(0, Math.min(100, Math.round(value)))}%`;
}

function estimatedLines(challenge: Challenge) {
  const estimate = challenge.estimated_lines;
  if (typeof estimate === "object") {
    return `${estimate.min.toLocaleString()}–${estimate.max.toLocaleString()}`;
  }
  return String(estimate);
}

function unique(values: string[]) {
  return Array.from(new Set(values)).sort((a, b) => a.localeCompare(b));
}

function issueUrl(node: ProgrammeNode) {
  const researchOpen = node.status === "research_open";
  const params = new URLSearchParams({
    template: researchOpen ? "research-intention.yml" : "claim.yml",
    title: `${researchOpen ? "[Research]" : "[Claim]"} ${node.id} — ${node.title}`,
  });
  return `${GITHUB}/issues/new?${params.toString()}`;
}

function stageProgress(stage: ProgrammeStage, nodes: ProgrammeNode[]) {
  const stageNodes = nodes.filter((node) => node.stage === stage.id);
  const earned = stageNodes.reduce(
    (sum, node) =>
      sum + node.weight_points * (node.completion.credit_percent / 100),
    0,
  );
  return {
    nodes: stageNodes,
    earned,
    percent: stage.weight_points ? (earned / stage.weight_points) * 100 : 0,
  };
}

function DependencyTags({
  ids,
  lookup,
  empty,
}: {
  ids: string[];
  lookup: Map<string, ProgrammeNode>;
  empty: string;
}) {
  if (!ids.length) return <span className="dependency-empty">{empty}</span>;

  return (
    <span className="dependency-tags">
      {ids.map((id) => (
        <span className="dependency-tag" key={id} title={lookup.get(id)?.title}>
          {id}
        </span>
      ))}
    </span>
  );
}

function LeanSignature({ challenge }: { challenge: Challenge }) {
  return (
    <div className="signature-block">
      <div className="signature-header">
        <span>Lean acceptance boundary</span>
        <span>{challenge.module}</span>
      </div>
      <div className="signature-declaration">
        <span>Declaration</span>
        <code>{challenge.declaration}</code>
      </div>
      <pre>
        <code>{challenge.signature ?? challenge.declaration}</code>
      </pre>
    </div>
  );
}

export function ProgrammeDashboard({
  programme,
}: {
  programme: Programme;
}) {
  const challengeNodes = useMemo(
    () =>
      programme.nodes.filter(
        (node) => node.challenge && node.challenge.claimable,
      ),
    [programme.nodes],
  );
  const nodeLookup = useMemo(
    () => new Map(programme.nodes.map((node) => [node.id, node])),
    [programme.nodes],
  );
  const statuses = useMemo(
    () => unique(challengeNodes.map((node) => node.status)),
    [challengeNodes],
  );
  const risks = useMemo(
    () => unique(challengeNodes.map((node) => node.risk)),
    [challengeNodes],
  );
  const backendOptions = useMemo(
    () => unique(challengeNodes.flatMap(backends)),
    [challengeNodes],
  );

  const [statusFilter, setStatusFilter] = useState("all");
  const [riskFilter, setRiskFilter] = useState("all");
  const [backendFilter, setBackendFilter] = useState("all");

  const filteredChallenges = useMemo(
    () =>
      challengeNodes.filter(
        (node) =>
          (statusFilter === "all" || node.status === statusFilter) &&
          (riskFilter === "all" || node.risk === riskFilter) &&
          (backendFilter === "all" ||
            backends(node).includes(backendFilter)),
      ),
    [backendFilter, challengeNodes, riskFilter, statusFilter],
  );

  const frontierNodes = useMemo(
    () =>
      programme.nodes
        .filter(
          (node) =>
            !node.challenge && node.completion.credit_percent < 100,
        )
        .sort((left, right) => {
          const riskOrder = { high: 3, medium: 2, low: 1 };
          const leftRisk =
            riskOrder[riskTone(left.risk) as keyof typeof riskOrder] ?? 0;
          const rightRisk =
            riskOrder[riskTone(right.risk) as keyof typeof riskOrder] ?? 0;
          return rightRisk - leftRisk || right.weight_points - left.weight_points;
        })
        .slice(0, 6),
    [programme.nodes],
  );

  const openChallengeCount = challengeNodes.filter((node) =>
    node.status.toLowerCase().includes("open"),
  ).length;
  const ordinaryChallengeCount = challengeNodes.filter(
    (node) => node.status === "open",
  ).length;
  const researchChallengeCount = challengeNodes.filter(
    (node) => node.status === "research_open",
  ).length;
  const integratedLines =
    typeof programme.baseline.integrated_lean_lines === "number"
      ? programme.baseline.integrated_lean_lines
      : 83_962;
  const integratedModules =
    typeof programme.baseline.integrated_lean_modules === "number"
      ? programme.baseline.integrated_lean_modules
      : 122;

  return (
    <div className="site-shell">
      <a className="skip-link" href="#main-content">
        Skip to programme
      </a>

      <header className="topbar">
        <a className="wordmark" href="#top" aria-label="Mazur Theorem home">
          <span className="wordmark-seal" aria-hidden="true">
            M
          </span>
          <span>
            <strong>Mazur Theorem</strong>
            <small>formalization programme</small>
          </span>
        </a>
        <nav className="primary-nav" aria-label="Primary navigation">
          <a href="#roadmap">Roadmap</a>
          <a href="#challenges">Challenges</a>
          <a href="#methodology">Method</a>
          <a className="nav-github" href={GITHUB}>
            GitHub <span aria-hidden="true">↗</span>
          </a>
        </nav>
      </header>

      <main id="main-content">
        <section className="hero" id="top">
          <div className="hero-copy">
            <p className="eyebrow">
              Open, kernel-checked mathematics · Lean 4
            </p>
            <h1>
              Mazur’s theorem,
              <span> one verified dependency at a time.</span>
            </h1>
            <p className="hero-deck">
              A public programme for the exact Lean Pool target: the rational
              torsion set of an elliptic curve over ℚ has ncard at most 16.
              The hard part is not hidden: every theorem, interface,
              dependency, and integration boundary is on the board.
            </p>
            <div className="hero-actions">
              <a className="button button-primary" href="#challenges">
                Find a challenge
                <span aria-hidden="true">↓</span>
              </a>
              <a
                className="button button-secondary"
                href={`${DOCUMENTATION}/blueprint/`}
              >
                Read the blueprint
                <span aria-hidden="true">↗</span>
              </a>
            </div>
            <dl className="hero-facts">
              <div>
                <dt>Checked Lean</dt>
                <dd>{integratedLines.toLocaleString()} lines</dd>
              </div>
              <div>
                <dt>Compiled modules</dt>
                <dd>{integratedModules}</dd>
              </div>
              <div>
                <dt>Open contracts</dt>
                <dd>
                  {openChallengeCount} boundaries ·{" "}
                  {programme.progress.claimable_open_points} pts
                </dd>
              </div>
            </dl>
          </div>

          <aside className="progress-ledger" aria-label="Programme progress">
            <div className="ledger-kicker">
              <span className="live-dot" aria-hidden="true" />
              Evidence-weighted ledger
            </div>
            <div className="progress-primary">
              <span
                className="progress-orbit"
                style={
                  {
                    "--progress": `${programme.progress.percent * 3.6}deg`,
                  } as React.CSSProperties
                }
                aria-hidden="true"
              >
                <span>{percentage(programme.progress.percent)}</span>
              </span>
              <div>
                <strong>Integrated</strong>
                <p>
                  {programme.progress.earned_points} of{" "}
                  {programme.progress.total_points} weighted points are
                  connected to a downstream consumer.
                </p>
              </div>
            </div>
            <div className="progress-comparison">
              <div className="comparison-heading">
                <span>Ecosystem-ready estimate</span>
                <strong>
                  {percentage(
                    programme.progress.ecosystem_ready_estimate_percent,
                  )}
                </strong>
              </div>
              <div className="meter" aria-hidden="true">
                <span
                  style={{
                    width: percentage(
                      programme.progress.ecosystem_ready_estimate_percent,
                    ),
                  }}
                />
              </div>
              <p>
                Includes plausible reusable work outside this repository.
                Porting, pin compatibility, and consumer tests are not yet
                credited as integrated.
              </p>
            </div>
            <a className="ledger-link" href="#methodology">
              Why these numbers are deliberately conservative
              <span aria-hidden="true">→</span>
            </a>
          </aside>
        </section>

        <section className="thesis-strip" aria-label="Programme principle">
          <p>
            <span>Programme principle</span>
            Progress is earned by use, not by volume: a definition reaches
            100% only when its proof is checked, its API is accepted, and a
            downstream theorem consumes it.
          </p>
        </section>

        <section className="section roadmap-section" id="roadmap">
          <div className="section-heading">
            <div>
              <p className="eyebrow">The weighted roadmap</p>
              <h2>A dependency graph with an honest denominator.</h2>
            </div>
            <p>
              The programme totals {programme.progress.total_points} points.
              Stage weights estimate effort across the whole theorem—not file
              counts, issue counts, or perceived mathematical elegance.
            </p>
          </div>

          <div className="roadmap-grid">
            {programme.stages.map((stage, index) => {
              const progress = stageProgress(stage, programme.nodes);
              const openInStage = progress.nodes.filter((node) =>
                node.status.toLowerCase().includes("open"),
              ).length;
              return (
                <article className="stage-card" key={stage.id}>
                  <div className="stage-index" aria-hidden="true">
                    {String(index + 1).padStart(2, "0")}
                  </div>
                  <div className="stage-card-body">
                    <div className="stage-title">
                      <div className="stage-meta">
                        <span>{stage.id}</span>
                        <span>{stage.weight_points} pts</span>
                      </div>
                      <h3>{stage.title}</h3>
                    </div>
                    <p>{stage.summary}</p>
                    <div className="stage-progress">
                      <div className="stage-progress-label">
                        <span>{percentage(progress.percent)} integrated</span>
                        <span>
                          {progress.nodes.length} nodes
                          {openInStage ? ` · ${openInStage} open` : ""}
                        </span>
                      </div>
                      <div className="meter" aria-hidden="true">
                        <span style={{ width: percentage(progress.percent) }} />
                      </div>
                    </div>
                  </div>
                </article>
              );
            })}
          </div>
        </section>

        <section className="section frontier-section" id="frontier">
          <div className="section-heading compact-heading">
            <div>
              <p className="eyebrow">Critical dependency frontier</p>
              <h2>The shared infrastructure that gates Mazur’s argument.</h2>
            </div>
            <p>
              These are coordination problems, not isolated bounties. Their
              interfaces should be owned centrally while proofs and vertical
              slices are distributed.
            </p>
          </div>

          <div className="frontier-grid">
            {frontierNodes.map((node) => (
              <article className="frontier-card" key={node.id}>
                <div className="card-topline">
                  <span className={`risk risk-${riskTone(node.risk)}`}>
                    {words(node.risk)} risk
                  </span>
                  <span>{node.weight_points} pts</span>
                </div>
                <p className="node-id">{node.id}</p>
                <h3>{node.title}</h3>
                <p>{node.summary}</p>
                <div className="backend-row">
                  {backends(node).map((backend) => (
                    <span className="backend" key={backend}>
                      {words(backend)}
                    </span>
                  ))}
                </div>
                <dl className="dependency-list">
                  <div>
                    <dt>Needs</dt>
                    <dd>
                      <DependencyTags
                        ids={node.depends_on}
                        lookup={nodeLookup}
                        empty="foundation node"
                      />
                    </dd>
                  </div>
                  <div>
                    <dt>Unlocks</dt>
                    <dd>
                      <DependencyTags
                        ids={node.unlocks}
                        lookup={nodeLookup}
                        empty="integration"
                      />
                    </dd>
                  </div>
                </dl>
              </article>
            ))}
          </div>
        </section>

        <section className="section challenges-section" id="challenges">
          <div className="section-heading challenge-heading">
            <div>
              <p className="eyebrow">Open contracts</p>
              <h2>Exact Lean interfaces for proof and research.</h2>
            </div>
            <p>
              Every card is an acceptance contract. There are{" "}
              {ordinaryChallengeCount} ordinary claims worth{" "}
              {programme.progress.ordinary_claimable_points} points and{" "}
              {researchChallengeCount} nonexclusive research intentions worth{" "}
              {programme.progress.research_open_points} points.
            </p>
          </div>

          <div className="filter-bar" aria-label="Challenge filters">
            <label>
              <span>Status</span>
              <select
                value={statusFilter}
                onChange={(event) => setStatusFilter(event.target.value)}
              >
                <option value="all">All statuses</option>
                {statuses.map((status) => (
                  <option key={status} value={status}>
                    {words(status)}
                  </option>
                ))}
              </select>
            </label>
            <label>
              <span>Risk</span>
              <select
                value={riskFilter}
                onChange={(event) => setRiskFilter(event.target.value)}
              >
                <option value="all">All risks</option>
                {risks.map((risk) => (
                  <option key={risk} value={risk}>
                    {words(risk)}
                  </option>
                ))}
              </select>
            </label>
            <label>
              <span>Backend</span>
              <select
                value={backendFilter}
                onChange={(event) => setBackendFilter(event.target.value)}
              >
                <option value="all">All backends</option>
                {backendOptions.map((backend) => (
                  <option key={backend} value={backend}>
                    {words(backend)}
                  </option>
                ))}
              </select>
            </label>
            <div className="filter-count" aria-live="polite">
              <strong>{filteredChallenges.length}</strong>
              <span>
                {filteredChallenges.length === 1 ? "challenge" : "challenges"}
              </span>
            </div>
          </div>

          <div className="challenge-list">
            {filteredChallenges.map((node) => {
              const challenge = node.challenge as Challenge;
              return (
                <article className="challenge-card" key={node.id}>
                  <div className="challenge-summary">
                    <div className="card-topline">
                      <span
                        className={`status status-${statusTone(node.status)}`}
                      >
                        {words(node.status)}
                      </span>
                      <span className={`risk risk-${riskTone(node.risk)}`}>
                        {words(node.risk)} risk
                      </span>
                    </div>
                    <p className="node-id">
                      {node.id} · {node.weight_points} points
                    </p>
                    <h3>{node.title}</h3>
                    <p className="challenge-informal">{challenge.informal}</p>
                    <div className="backend-row">
                      {backends(node).map((backend) => (
                        <span className="backend" key={backend}>
                          {words(backend)}
                        </span>
                      ))}
                      <span className="readiness">{words(node.readiness)}</span>
                    </div>
                    <dl className="challenge-details">
                      <div>
                        <dt>Estimated proof</dt>
                        <dd>{estimatedLines(challenge)} Lean lines</dd>
                      </div>
                      <div>
                        <dt>Suggested route</dt>
                        <dd>{challenge.recommended_route}</dd>
                      </div>
                      <div>
                        <dt>Skills</dt>
                        <dd>{challenge.skills.join(" · ")}</dd>
                      </div>
                    </dl>
                    {node.status === "research_open" && (
                      <p className="coordination-note">
                        Parallel approaches are welcome for this research-open
                        boundary.
                      </p>
                    )}
                    <div className="challenge-actions">
                      <a className="button button-primary" href={issueUrl(node)}>
                        {node.status === "research_open"
                          ? "Register an approach"
                          : "Claim this challenge"}
                        <span aria-hidden="true">↗</span>
                      </a>
                      <a
                        className="text-link"
                        href={`${GITHUB}/blob/main/${challenge.file}`}
                      >
                        View source <span aria-hidden="true">→</span>
                      </a>
                    </div>
                  </div>

                  <div className="challenge-contract">
                    <LeanSignature challenge={challenge} />
                    <div className="contract-grid">
                      <div>
                        <h4>Imports</h4>
                        <ul className="code-list">
                          {challenge.imports.map((item) => (
                            <li key={item}>
                              <code>{item}</code>
                            </li>
                          ))}
                        </ul>
                      </div>
                      <div>
                        <h4>Consumed by</h4>
                        <ul className="code-list">
                          {challenge.consumer_declarations.map((item) => (
                            <li key={item}>
                              <code>{item}</code>
                            </li>
                          ))}
                        </ul>
                      </div>
                      <div>
                        <h4>Destination</h4>
                        <ul className="code-list">
                          <li>
                            <code>{challenge.destination_module}</code>
                          </li>
                          <li>
                            <code>{challenge.destination_declaration}</code>
                          </li>
                        </ul>
                      </div>
                    </div>
                    <dl className="dependency-list horizontal">
                      <div>
                        <dt>Depends on</dt>
                        <dd>
                          <DependencyTags
                            ids={node.depends_on}
                            lookup={nodeLookup}
                            empty="ready at current pin"
                          />
                        </dd>
                      </div>
                      <div>
                        <dt>Unlocks</dt>
                        <dd>
                          <DependencyTags
                            ids={node.unlocks}
                            lookup={nodeLookup}
                            empty="direct integration"
                          />
                        </dd>
                      </div>
                    </dl>
                  </div>
                </article>
              );
            })}
          </div>

          {!filteredChallenges.length && (
            <div className="empty-state">
              <p>No challenge matches this combination.</p>
              <button
                type="button"
                onClick={() => {
                  setStatusFilter("all");
                  setRiskFilter("all");
                  setBackendFilter("all");
                }}
              >
                Clear filters
              </button>
            </div>
          )}
        </section>

        <section className="section method-section" id="methodology">
          <div className="method-panel">
            <div>
              <p className="eyebrow">How progress is scored</p>
              <h2>Four gates. One weighted ledger.</h2>
              <p className="method-lead">{programme.progress.method}</p>
            </div>
            <ol className="gate-list">
              <li>
                <span>01</span>
                <div>
                  <strong>Statement</strong>
                  <p>The formal declaration faithfully matches the mathematics.</p>
                </div>
              </li>
              <li>
                <span>02</span>
                <div>
                  <strong>Kernel proof</strong>
                  <p>Lean accepts it without project-specific axioms or placeholders.</p>
                </div>
              </li>
              <li>
                <span>03</span>
                <div>
                  <strong>API accepted</strong>
                  <p>Definitions pass mathematical sanity checks and review.</p>
                </div>
              </li>
              <li>
                <span>04</span>
                <div>
                  <strong>Integrated</strong>
                  <p>A named downstream consumer compiles against the result.</p>
                </div>
              </li>
            </ol>
          </div>

          <div className="caveat-panel">
            <div className="caveat-mark" aria-hidden="true">
              ≠
            </div>
            <div>
              <h3>What 5% does—and does not—mean</h3>
              <p>
                It is an effort-weighted planning estimate, not a theorem of
                project management. The denominator is uncertain because
                Jacobians, integral modular curves, Néron models, and the
                Eisenstein quotient do not yet share a tested Lean spine.
              </p>
              <p>
                The ≈
                {programme.progress.ecosystem_ready_estimate_percent}%
                ecosystem-ready figure is deliberately shown separately. It
                counts work that may be reusable from Lean Pool, Tau Ceti,
                FLT, and other audited repositories, but it earns integrated
                credit only after porting and consumer tests. Percentages will
                move as interfaces reveal the real work.
              </p>
              <div className="source-links">
                <a href={`${GITHUB}/blob/main/coordination/program.json`}>
                  Inspect the ledger <span aria-hidden="true">↗</span>
                </a>
                <a href={`${GITHUB}/blob/main/docs/PROGRESS_METHOD.md`}>
                  Read the methodology <span aria-hidden="true">↗</span>
                </a>
              </div>
            </div>
          </div>
        </section>

        <section className="contribute-section" id="contribute">
          <div>
            <p className="eyebrow">Join the programme</p>
            <h2>Pick a boundary. Prove it. Connect it.</h2>
            <p>
              Contributors get an exact declaration, pinned dependencies, a
              named consumer, and review criteria. Maintainers coordinate the
              shared architecture so independent work composes.
            </p>
          </div>
          <div className="contribute-actions">
            <a className="button button-light" href={`${GITHUB}/blob/main/CONTRIBUTING.md`}>
              Contribution guide <span aria-hidden="true">↗</span>
            </a>
            <a className="button button-outline-light" href={`${GITHUB}/issues`}>
              Discuss an issue <span aria-hidden="true">↗</span>
            </a>
          </div>
        </section>
      </main>

      <footer>
        <div className="footer-wordmark">
          <span className="wordmark-seal" aria-hidden="true">
            M
          </span>
          <p>
            <strong>Mazur Theorem</strong>
            <span>Open formal mathematics, checked by Lean.</span>
          </p>
        </div>
        <div className="footer-links">
          <a href={GITHUB}>Repository</a>
          <a href={`${DOCUMENTATION}/blueprint/`}>Blueprint</a>
          <a href={`${DOCUMENTATION}/exposition/`}>Exposition</a>
          <a href={`${DOCUMENTATION}/docs/`}>API docs</a>
          <a href="https://github.com/TauCetiProject/TauCeti">Tau Ceti</a>
          <a href="https://github.com/Vilin97/lean-pool">Lean Pool</a>
        </div>
        <p className="footer-note">
          Progress data: programme schema v{programme.schema_version}. Apache
          2.0.
        </p>
      </footer>
    </div>
  );
}

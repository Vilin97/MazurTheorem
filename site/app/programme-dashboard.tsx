"use client";

import { useMemo, useState } from "react";
import type {
  Challenge,
  ExternalReuse,
  Programme,
  ProgrammeArtifact,
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

function graphStageTitle(value: string) {
  const conciseTitles: Record<string, string> = {
    "Shared algebraic geometry and isogenies": "Shared geometry",
    "Prime-level infrastructure": "Prime infrastructure",
    "Mazur's prime-order argument": "Prime argument",
    "Integration and hardening": "Integration",
  };
  return conciseTitles[value] ?? value;
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
  onSelect,
}: {
  ids: string[];
  lookup: Map<string, ProgrammeNode>;
  empty: string;
  onSelect: (id: string) => void;
}) {
  if (!ids.length) return <span className="dependency-empty">{empty}</span>;

  return (
    <span className="dependency-tags">
      {ids.map((id) => (
        <button
          className="dependency-tag"
          key={id}
          title={`Open ${lookup.get(id)?.title ?? id}`}
          type="button"
          onClick={() => onSelect(id)}
        >
          {id}
        </button>
      ))}
    </span>
  );
}

function nodeArtifacts(node: ProgrammeNode): ProgrammeArtifact[] {
  if (node.artifacts?.length) return node.artifacts;

  if (node.challenge) {
    return [
      {
        kind: "theorem",
        name:
          node.challenge.destination_declaration || node.challenge.declaration,
        state: "contract",
        description: node.challenge.informal,
        module: node.challenge.destination_module || node.challenge.module,
        declaration: node.challenge.declaration,
        signature: node.challenge.signature,
      },
    ];
  }

  return [];
}

function ArtifactList({
  artifacts,
  compact = false,
}: {
  artifacts: ProgrammeArtifact[];
  compact?: boolean;
}) {
  return (
    <ul className={`artifact-list${compact ? " artifact-list-compact" : ""}`}>
      {artifacts.map((artifact, index) => (
        <li key={`${artifact.kind}-${artifact.name}-${index}`}>
          <div className="artifact-heading">
            <span>{artifact.kind}</span>
            <span>{words(artifact.state)}</span>
          </div>
          <code>{artifact.name}</code>
          <p>{artifact.description}</p>
          {(artifact.module || artifact.declaration) && (
            <div className="artifact-location">
              {artifact.module && <code>{artifact.module}</code>}
              {artifact.declaration &&
                artifact.declaration !== artifact.name && (
                  <code>{artifact.declaration}</code>
                )}
            </div>
          )}
          {artifact.signature && (
            <pre className="artifact-signature">
              <code>{artifact.signature}</code>
            </pre>
          )}
        </li>
      ))}
    </ul>
  );
}

function ExternalReuseList({ entries }: { entries: ExternalReuse[] }) {
  return (
    <ul className="external-reuse-list">
      {entries.map((entry, index) => (
        <li key={`${entry.source}-${index}`}>
          <dl className="external-reuse-facts">
            <div>
              <dt>Source</dt>
              <dd>{entry.source}</dd>
            </div>
            <div>
              <dt>Status</dt>
              <dd>{words(entry.status)}</dd>
            </div>
            <div className="external-reuse-estimate">
              <dt>Planning estimate</dt>
              <dd>
                {entry.estimated_node_savings_percent.min}–
                {entry.estimated_node_savings_percent.max}% node savings
              </dd>
            </div>
          </dl>
          <div className="external-reuse-copy">
            <p>
              <strong>Reusable substrate</strong>
              {entry.summary}
            </p>
            <p>
              <strong>Audit boundary</strong>
              {entry.boundary}
            </p>
          </div>
          {entry.declarations.length > 0 && (
            <div className="external-reuse-declarations">
              <p>Audited declarations</p>
              <ul>
                {entry.declarations.map((declaration) => (
                  <li key={`${declaration.name}-${declaration.url}`}>
                    <a href={declaration.url}>{declaration.name}</a>
                  </li>
                ))}
              </ul>
            </div>
          )}
        </li>
      ))}
    </ul>
  );
}

function NodeDetail({
  node,
  stage,
  lookup,
  onSelect,
}: {
  node: ProgrammeNode;
  stage: ProgrammeStage | undefined;
  lookup: Map<string, ProgrammeNode>;
  onSelect: (id: string) => void;
}) {
  return (
    <aside
      className="node-detail-panel"
      id="node-detail"
      aria-labelledby="node-detail-title"
    >
      <div className="node-detail-heading">
        <div>
          <p className="node-id">{node.id}</p>
          <h3 id="node-detail-title">{node.title}</h3>
        </div>
        <div className="node-detail-badges">
          <span className={`status status-${statusTone(node.status)}`}>
            {words(node.status)}
          </span>
          <span className={`risk risk-${riskTone(node.risk)}`}>
            {words(node.risk)} risk
          </span>
        </div>
      </div>
      <p className="node-detail-summary">{node.summary}</p>
      <dl className="node-facts">
        <div>
          <dt>Stage</dt>
          <dd>{stage?.title ?? words(node.stage)}</dd>
        </div>
        <div>
          <dt>Weight</dt>
          <dd>{node.weight_points} points</dd>
        </div>
        <div>
          <dt>Readiness</dt>
          <dd>{words(node.readiness)}</dd>
        </div>
        <div>
          <dt>Backend</dt>
          <dd>{backends(node).map(words).join(" · ")}</dd>
        </div>
      </dl>
      <div className="node-detail-artifacts">
        <h4>Definitions, theorems, and API surface</h4>
        <ArtifactList artifacts={nodeArtifacts(node)} />
      </div>
      {node.external_reuse && node.external_reuse.length > 0 && (
        <section
          className="external-reuse"
          aria-labelledby={`external-reuse-title-${node.id}`}
        >
          <div className="external-reuse-heading">
            <span aria-hidden="true">↗</span>
            <h4 id={`external-reuse-title-${node.id}`}>
              Audited external substrate
            </h4>
          </div>
          <ExternalReuseList entries={node.external_reuse} />
        </section>
      )}
      <dl className="dependency-list horizontal node-detail-dependencies">
        <div>
          <dt>Depends on</dt>
          <dd>
            <DependencyTags
              ids={node.depends_on}
              lookup={lookup}
              empty="foundation node"
              onSelect={onSelect}
            />
          </dd>
        </div>
        <div>
          <dt>Unlocks</dt>
          <dd>
            <DependencyTags
              ids={node.unlocks}
              lookup={lookup}
              empty="final integration"
              onSelect={onSelect}
            />
          </dd>
        </div>
      </dl>
    </aside>
  );
}

const GRAPH_COLUMN_WIDTH = 232;
const GRAPH_NODE_WIDTH = 196;
const GRAPH_NODE_HEIGHT = 35;
const GRAPH_ROW_HEIGHT = 49;
const GRAPH_TOP = 72;

function DependencyGraph({
  programme,
  selectedNodeId,
  lookup,
  onSelect,
}: {
  programme: Programme;
  selectedNodeId: string;
  lookup: Map<string, ProgrammeNode>;
  onSelect: (id: string) => void;
}) {
  const [focusStage, setFocusStage] = useState("all");
  const stageIndex = useMemo(
    () => new Map(programme.stages.map((stage, index) => [stage.id, index])),
    [programme.stages],
  );
  const nodesByStage = useMemo(
    () =>
      programme.stages.map((stage) =>
        programme.nodes.filter((node) => node.stage === stage.id),
      ),
    [programme.nodes, programme.stages],
  );
  const positions = useMemo(() => {
    const result = new Map<string, { x: number; y: number }>();
    nodesByStage.forEach((nodes, column) => {
      nodes.forEach((node, row) => {
        result.set(node.id, {
          x: 20 + column * GRAPH_COLUMN_WIDTH,
          y: GRAPH_TOP + row * GRAPH_ROW_HEIGHT,
        });
      });
    });
    return result;
  }, [nodesByStage]);
  const focusedIds = useMemo(() => {
    if (focusStage === "all")
      return new Set(programme.nodes.map((node) => node.id));
    const ids = new Set<string>();
    programme.nodes.forEach((node) => {
      if (node.stage === focusStage) {
        ids.add(node.id);
        node.depends_on.forEach((id) => ids.add(id));
        node.unlocks.forEach((id) => ids.add(id));
      }
    });
    return ids;
  }, [focusStage, programme.nodes]);
  const graphHeight =
    GRAPH_TOP +
    Math.max(...nodesByStage.map((nodes) => nodes.length), 1) *
      GRAPH_ROW_HEIGHT +
    24;
  const graphWidth =
    40 + (programme.stages.length - 1) * GRAPH_COLUMN_WIDTH + GRAPH_NODE_WIDTH;

  return (
    <div className="dependency-graph-shell">
      <div className="graph-toolbar">
        <div>
          <span className="graph-toolbar-label">Graph focus</span>
          <div
            className="graph-focus-controls"
            aria-label="Focus graph by stage"
          >
            <button
              type="button"
              className={focusStage === "all" ? "is-active" : undefined}
              aria-pressed={focusStage === "all"}
              onClick={() => setFocusStage("all")}
            >
              {`All ${programme.nodes.length} nodes`}
            </button>
            {programme.stages.map((stage, index) => (
              <button
                type="button"
                key={stage.id}
                aria-label={`Focus graph on stage ${index + 1}: ${stage.title}`}
                className={focusStage === stage.id ? "is-active" : undefined}
                aria-pressed={focusStage === stage.id}
                onClick={() => setFocusStage(stage.id)}
              >
                {String(index + 1).padStart(2, "0")}
              </button>
            ))}
          </div>
        </div>
        <div className="graph-legend" aria-label="Graph legend">
          <span>
            <i className="legend-complete" /> Integrated
          </span>
          <span>
            <i className="legend-open" /> Open
          </span>
          <span>
            <i className="legend-planned" /> Planned or blocked
          </span>
        </div>
      </div>

      <div className="dependency-graph-scroller" tabIndex={0}>
        <svg
          className="dependency-graph"
          viewBox={`0 0 ${graphWidth} ${graphHeight}`}
          width={graphWidth}
          height={graphHeight}
          role="group"
          aria-labelledby="dependency-graph-title dependency-graph-description"
        >
          <title id="dependency-graph-title">
            Mazur theorem dependency graph
          </title>
          <desc id="dependency-graph-description">
            {`${programme.nodes.length} formalization nodes arranged in ${programme.stages.length} stage columns. Select a node to inspect its exact scope.`}
          </desc>
          <defs>
            <marker
              id="graph-arrow"
              markerWidth="8"
              markerHeight="8"
              refX="7"
              refY="4"
              orient="auto"
              markerUnits="strokeWidth"
            >
              <path d="M 0 0 L 8 4 L 0 8 z" />
            </marker>
          </defs>
          {programme.stages.map((stage, column) => (
            <g className="graph-stage-label" key={stage.id}>
              <title>{stage.title}</title>
              <text x={20 + column * GRAPH_COLUMN_WIDTH} y={23}>
                {String(column + 1).padStart(2, "0")} ·{" "}
                {graphStageTitle(stage.title)}
              </text>
              <text x={20 + column * GRAPH_COLUMN_WIDTH} y={42}>
                {nodesByStage[column].length} nodes · {stage.weight_points} pts
              </text>
            </g>
          ))}
          <g className="graph-edges" aria-hidden="true">
            {programme.nodes.flatMap((node) =>
              node.depends_on.map((dependencyId) => {
                const source = positions.get(dependencyId);
                const target = positions.get(node.id);
                if (!source || !target) return null;
                const sourceColumn =
                  stageIndex.get(lookup.get(dependencyId)?.stage ?? "") ?? 0;
                const targetColumn = stageIndex.get(node.stage) ?? 0;
                const sameColumn = sourceColumn === targetColumn;
                const startX = sameColumn
                  ? source.x + GRAPH_NODE_WIDTH - 5
                  : source.x + GRAPH_NODE_WIDTH;
                const startY = source.y + GRAPH_NODE_HEIGHT / 2;
                const endX = sameColumn
                  ? target.x + GRAPH_NODE_WIDTH - 5
                  : target.x;
                const endY = target.y + GRAPH_NODE_HEIGHT / 2;
                const bend = sameColumn
                  ? source.x + GRAPH_NODE_WIDTH + 15
                  : (startX + endX) / 2;
                const focused =
                  focusedIds.has(node.id) && focusedIds.has(dependencyId);
                return (
                  <path
                    key={`${dependencyId}-${node.id}`}
                    className={focused ? undefined : "is-muted"}
                    d={`M ${startX} ${startY} C ${bend} ${startY}, ${bend} ${endY}, ${endX} ${endY}`}
                    markerEnd="url(#graph-arrow)"
                  />
                );
              }),
            )}
          </g>
          <g className="graph-nodes">
            {programme.nodes.map((node) => {
              const point = positions.get(node.id);
              if (!point) return null;
              const selected = node.id === selectedNodeId;
              const focused = focusedIds.has(node.id);
              return (
                <g
                  className={`graph-node graph-node-${statusTone(node.status)}${selected ? " is-selected" : ""}${focused ? "" : " is-muted"}`}
                  key={node.id}
                  role="button"
                  tabIndex={0}
                  aria-label={`${node.id}: ${node.title}, ${words(node.status)}`}
                  aria-pressed={selected}
                  transform={`translate(${point.x} ${point.y})`}
                  onClick={() => onSelect(node.id)}
                  onKeyDown={(event) => {
                    if (event.key === "Enter" || event.key === " ") {
                      event.preventDefault();
                      onSelect(node.id);
                    }
                  }}
                >
                  <title>{node.title}</title>
                  <rect
                    width={GRAPH_NODE_WIDTH}
                    height={GRAPH_NODE_HEIGHT}
                    rx="3"
                  />
                  <circle cx="13" cy={GRAPH_NODE_HEIGHT / 2} r="4" />
                  <text x="23" y="14">
                    {node.id}
                  </text>
                  <text x="23" y="27">
                    {node.weight_points} pts · {words(node.status)}
                  </text>
                </g>
              );
            })}
          </g>
        </svg>
      </div>

      <details className="graph-accessible-list">
        <summary>Browse the graph as a dependency list</summary>
        <ol>
          {programme.stages.map((stage) => (
            <li key={stage.id}>
              <strong>{stage.title}</strong>
              <ul>
                {programme.nodes
                  .filter((node) => node.stage === stage.id)
                  .map((node) => (
                    <li key={node.id}>
                      <button type="button" onClick={() => onSelect(node.id)}>
                        <code>{node.id}</code> — {node.title}
                      </button>
                      <span>
                        {node.depends_on.length
                          ? `Needs ${node.depends_on.join(", ")}`
                          : "Foundation node"}
                      </span>
                    </li>
                  ))}
              </ul>
            </li>
          ))}
        </ol>
      </details>
    </div>
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

export function ProgrammeDashboard({ programme }: { programme: Programme }) {
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
  const [selectedStageId, setSelectedStageId] = useState(
    programme.stages[0]?.id ?? "",
  );
  const [selectedNodeId, setSelectedNodeId] = useState(
    programme.nodes[0]?.id ?? "",
  );

  const selectedNode = nodeLookup.get(selectedNodeId) ?? programme.nodes[0];
  const selectedNodeStage = programme.stages.find(
    (stage) => stage.id === selectedNode?.stage,
  );

  function selectNode(id: string) {
    const node = nodeLookup.get(id);
    if (!node) return;
    setSelectedNodeId(id);
    setSelectedStageId(node.stage);
    window.requestAnimationFrame(() => {
      const reducedMotion = window.matchMedia(
        "(prefers-reduced-motion: reduce)",
      ).matches;
      document.getElementById("node-detail")?.scrollIntoView({
        behavior: reducedMotion ? "auto" : "smooth",
        block: "nearest",
      });
    });
  }

  const filteredChallenges = useMemo(
    () =>
      challengeNodes.filter(
        (node) =>
          (statusFilter === "all" || node.status === statusFilter) &&
          (riskFilter === "all" || node.risk === riskFilter) &&
          (backendFilter === "all" || backends(node).includes(backendFilter)),
      ),
    [backendFilter, challengeNodes, riskFilter, statusFilter],
  );

  const frontierNodes = useMemo(
    () =>
      programme.nodes
        .filter(
          (node) => !node.challenge && node.completion.credit_percent < 100,
        )
        .sort((left, right) => {
          const riskOrder = { high: 3, medium: 2, low: 1 };
          const leftRisk =
            riskOrder[riskTone(left.risk) as keyof typeof riskOrder] ?? 0;
          const rightRisk =
            riskOrder[riskTone(right.risk) as keyof typeof riskOrder] ?? 0;
          return (
            rightRisk - leftRisk || right.weight_points - left.weight_points
          );
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
      : 168;

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
          <a href="#dependency-graph">Graph</a>
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
            <p className="eyebrow">Open, kernel-checked mathematics · Lean 4</p>
            <h1>
              Mazur’s theorem,
              <span> one verified dependency at a time.</span>
            </h1>
            <p className="hero-deck">
              A public programme for the exact Lean Pool target: the rational
              torsion set of an elliptic curve over ℚ has ncard at most 16. The
              hard part is not hidden: every theorem, interface, dependency, and
              integration boundary is on the board.
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
            Progress is earned by use, not by volume: a definition reaches 100%
            only when its proof is checked, its API is accepted, and a
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
              const selected = selectedStageId === stage.id;
              const deliverables = stage.deliverables?.length
                ? stage.deliverables
                : progress.nodes.flatMap(nodeArtifacts);
              return (
                <div
                  className={`stage-record${selected ? " is-selected" : ""}`}
                  key={stage.id}
                >
                  <button
                    className="stage-card"
                    type="button"
                    aria-expanded={selected}
                    aria-controls={`stage-details-${stage.id}`}
                    onClick={() => setSelectedStageId(selected ? "" : stage.id)}
                  >
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
                          <span
                            style={{ width: percentage(progress.percent) }}
                          />
                        </div>
                      </div>
                    </div>
                    <span className="stage-disclosure" aria-hidden="true">
                      {selected ? "Close scope" : "Open scope"}
                      <i>{selected ? "−" : "+"}</i>
                    </span>
                  </button>

                  <div
                    className="stage-details"
                    id={`stage-details-${stage.id}`}
                    hidden={!selected}
                  >
                      <section
                        className="stage-deliverables"
                        aria-labelledby={`stage-contract-${stage.id}`}
                      >
                        <div className="stage-details-heading">
                          <div>
                            <p className="eyebrow">Stage contract</p>
                            <h3 id={`stage-contract-${stage.id}`}>
                              What this stage must define and prove
                            </h3>
                          </div>
                          <p>
                            These are the concrete APIs and results that count
                            as this stage’s scope. Node cards below show how the
                            work is divided and connected.
                          </p>
                        </div>
                        <ArtifactList artifacts={deliverables} />
                      </section>

                      <section
                        className="stage-node-section"
                        aria-labelledby={`stage-nodes-${stage.id}`}
                      >
                        <div className="stage-node-heading">
                          <h3 id={`stage-nodes-${stage.id}`}>
                            All {progress.nodes.length} dependency nodes
                          </h3>
                          <span>
                            {progress.earned.toFixed(1)} of{" "}
                            {stage.weight_points} points integrated
                          </span>
                        </div>
                        <div className="stage-node-grid">
                          {progress.nodes.map((node) => (
                            <article className="stage-node-card" key={node.id}>
                              <div className="stage-node-topline">
                                <span
                                  className={`status status-${statusTone(node.status)}`}
                                >
                                  {words(node.status)}
                                </span>
                                <span>{node.weight_points} pts</span>
                              </div>
                              <button
                                className="stage-node-title"
                                type="button"
                                onClick={() => selectNode(node.id)}
                              >
                                <code>{node.id}</code>
                                <strong>{node.title}</strong>
                                <span aria-hidden="true">Open detail →</span>
                              </button>
                              <p>{node.summary}</p>
                              <ArtifactList
                                artifacts={nodeArtifacts(node)}
                                compact
                              />
                              <dl className="stage-node-dependencies">
                                <div>
                                  <dt>Needs</dt>
                                  <dd>
                                    <DependencyTags
                                      ids={node.depends_on}
                                      lookup={nodeLookup}
                                      empty="foundation node"
                                      onSelect={selectNode}
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
                                      onSelect={selectNode}
                                    />
                                  </dd>
                                </div>
                              </dl>
                            </article>
                          ))}
                        </div>
                      </section>
                  </div>
                </div>
              );
            })}
          </div>
        </section>

        <section className="section graph-section" id="dependency-graph">
          <div className="section-heading">
            <div>
              <p className="eyebrow">Interactive dependency graph</p>
              <h2>Every node, edge, and hand-off.</h2>
            </div>
            <p>
              Read left to right across the six programme stages. Select any
              node to inspect its definitions, theorem contracts, dependencies,
              and downstream consumers.
            </p>
          </div>
          <div className="graph-explorer-layout">
            <DependencyGraph
              programme={programme}
              selectedNodeId={selectedNode?.id ?? ""}
              lookup={nodeLookup}
              onSelect={selectNode}
            />
            {selectedNode && (
              <NodeDetail
                node={selectedNode}
                stage={selectedNodeStage}
                lookup={nodeLookup}
                onSelect={selectNode}
              />
            )}
          </div>
          <p className="graph-blueprint-link">
            Prefer a theorem-first view? The canonical Verso blueprint includes
            proof-status summaries and its own interactive dependency graph.{" "}
            <a href={`${DOCUMENTATION}/blueprint/`}>
              Open the formal blueprint <span aria-hidden="true">↗</span>
            </a>
          </p>
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
                        onSelect={selectNode}
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
                        onSelect={selectNode}
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
                      <a
                        className="button button-primary"
                        href={issueUrl(node)}
                      >
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
                            onSelect={selectNode}
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
                            onSelect={selectNode}
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
                  <p>
                    The formal declaration faithfully matches the mathematics.
                  </p>
                </div>
              </li>
              <li>
                <span>02</span>
                <div>
                  <strong>Kernel proof</strong>
                  <p>
                    Lean accepts it without project-specific axioms or
                    placeholders.
                  </p>
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
                  <p>
                    A named downstream consumer compiles against the result.
                  </p>
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
                The ≈{programme.progress.ecosystem_ready_estimate_percent}%
                ecosystem-ready figure is deliberately shown separately. It
                counts work that may be reusable from Lean Pool, Tau Ceti, FLT,
                and other audited repositories, but it earns integrated credit
                only after porting and consumer tests. Percentages will move as
                interfaces reveal the real work.
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
            <a
              className="button button-light"
              href={`${GITHUB}/blob/main/CONTRIBUTING.md`}
            >
              Contribution guide <span aria-hidden="true">↗</span>
            </a>
            <a
              className="button button-outline-light"
              href={`${GITHUB}/issues`}
            >
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

export type Completion = {
  statement: boolean;
  proof: boolean;
  api: boolean;
  integrated: boolean;
  credit_percent: number;
};

export type Challenge = {
  claimable?: boolean;
  module: string;
  file: string;
  declaration: string;
  signature?: string;
  imports: string[];
  informal: string;
  recommended_route: string;
  consumer_declarations: string[];
  destination_module: string;
  destination_declaration: string;
  estimated_lines:
    | number
    | string
    | {
        min: number;
        max: number;
      };
  skills: string[];
};

export type ProgrammeArtifact = {
  kind: "audit" | "definition" | "integration" | "structure" | "theorem";
  name: string;
  state: "contract" | "integrated" | "proposed";
  description: string;
  module?: string;
  declaration?: string;
  signature?: string;
};

export type WorkPackage = {
  id: string;
  title: string;
  weight_points: number;
  status: "active" | "blocked" | "integrated" | "next" | "paused";
  depends_on: string[];
  exit_criterion: string;
};

export type NodeEvidence = {
  recorded_artifact_count: number;
  canonical_artifact_count: number;
  policy: string;
};

export type ExternalReuseDeclaration = {
  name: string;
  url: string;
};

export type ExternalReuse = {
  source: string;
  status: string;
  estimated_node_savings_percent: {
    min: number;
    max: number;
  };
  summary: string;
  boundary: string;
  declarations: ExternalReuseDeclaration[];
};

export type ProgrammeNode = {
  id: string;
  title: string;
  stage: string;
  kind: string;
  status: string;
  readiness: string;
  weight_points: number;
  risk: string;
  backend: string | string[];
  summary: string;
  depends_on: string[];
  unlocks: string[];
  completion: Completion;
  artifacts?: ProgrammeArtifact[];
  work_packages?: WorkPackage[];
  evidence?: NodeEvidence;
  external_reuse?: ExternalReuse[];
  challenge?: Challenge;
};

export type ProgrammeStage = {
  id: string;
  title: string;
  weight_points: number;
  summary: string;
  deliverables?: ProgrammeArtifact[];
};

export type ProgrammeEndpoint = {
  name: string;
  signature: string;
  meaning?: string;
  note?: string;
};

export type ActiveLane = {
  id: string;
  title: string;
  node_ids: string[];
  current_work_package: string;
  exit_criterion: string;
};

export type ProgrammeExecution = {
  revision: {
    id: string;
    date: string;
    summary: string;
  };
  canonical_target: ProgrammeEndpoint;
  challenge_corollary: ProgrammeEndpoint;
  proof_route: {
    id: string;
    public_boundary: string;
    proposed_witness: string;
    private_constructor: string;
    decision: string;
  };
  work_in_progress_limit: number;
  active_lanes: ActiveLane[];
  paused_node_ids: string[];
  paused_policy: string;
};

export type ReleaseEndpoint = {
  id: string;
  owner_node: string;
  declaration: string;
  state: "integrated" | "proposed";
  depends_on: string[];
  role: "canonical" | "challenge_corollary";
};

export type Programme = {
  schema_version: number | string;
  title: string;
  execution: ProgrammeExecution;
  release_endpoints: ReleaseEndpoint[];
  baseline: {
    integrated_lean_lines: number;
    integrated_lean_modules: number;
    [key: string]: unknown;
  };
  sources: unknown;
  progress: {
    total_points: number;
    earned_points: number;
    percent: number;
    ecosystem_ready_estimate_percent: number;
    claimable_open_points: number;
    ordinary_claimable_points: number;
    research_open_points: number;
    method: string;
  };
  stages: ProgrammeStage[];
  nodes: ProgrammeNode[];
};

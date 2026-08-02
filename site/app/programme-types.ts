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

export type Programme = {
  schema_version: number | string;
  title: string;
  baseline: Record<string, unknown>;
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
